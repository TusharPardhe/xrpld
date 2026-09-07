// Legacy catchup loop removed; NetworkOpsStrand handles all consensus duties.

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

// Configure jemalloc to immediately return freed pages to the OS.
// Without this, jemalloc retains freed pages as "dirty" for potential reuse,
// so RSS never decreases even after freeing 7.5M tree nodes (33GB+).
// dirty_decay_ms:0 = purge dirty pages immediately
// muzzy_decay_ms:0 = purge muzzy pages immediately
#[cfg(not(target_env = "msvc"))]
#[used]
#[allow(non_upper_case_globals)]
#[unsafe(no_mangle)]
pub static _rjem_malloc_conf: Option<&'static libc::c_char> = Some(unsafe {
    &*c"dirty_decay_ms:0,muzzy_decay_ms:0"
        .as_ptr()
        .cast::<libc::c_char>()
});

use app::{
    AppBootstrapOptions, AppBootstrapRuntime, MainRuntime, ManagedComponent, build_bootstrap_root,
    load_basic_config_file, parse_bootstrap_args, run_bootstrap_runtime,
};
#[cfg(test)]
use basics::base_uint::Uint256;
use basics::basic_config::BasicConfig;
use basics::uptime_clock::UptimeClock;
use indicatif::{ProgressBar, ProgressStyle};
use rpc::rpc_cmd_to_json;
use server::{ServerRuntime, ServerRuntimeBuildReport};
#[cfg(test)]
use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::Path;
#[cfg(test)]
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::{Duration, Instant};

#[cfg(test)]
const PEERFINDER_LIVE_CACHE_TTL: Duration = Duration::from_secs(30);
#[cfg(test)]
const PEERFINDER_RECENT_ATTEMPT_DURATION: Duration = Duration::from_secs(60);
#[cfg(test)]
const PEERFINDER_MAX_HOPS: u32 = 6;
#[cfg(test)]
const PEERFINDER_NUMBER_OF_ENDPOINTS: usize = (2 * PEERFINDER_MAX_HOPS) as usize;
#[cfg(test)]
const PEERFINDER_MAX_CONNECT_ATTEMPTS: usize = 20;
#[cfg(test)]
const PEERFINDER_OUT_PERCENT: usize = 15;
#[cfg(test)]
const PEERFINDER_MIN_OUTBOUND: usize = 10;

#[cfg(test)]
#[derive(Debug, Clone, Copy)]
struct KnownEndpoint {
    hops: u32,
    last_seen: Instant,
}

#[cfg(test)]
fn remember_known_endpoint(
    known_endpoints: &mut HashMap<std::net::SocketAddr, KnownEndpoint>,
    endpoint: std::net::SocketAddr,
    hops: u32,
    now: Instant,
) {
    known_endpoints
        .entry(endpoint)
        .and_modify(|known| {
            known.hops = known.hops.min(hops);
            known.last_seen = now;
        })
        .or_insert(KnownEndpoint {
            hops,
            last_seen: now,
        });
}

#[cfg(test)]
fn prune_known_endpoints(
    known_endpoints: &mut HashMap<std::net::SocketAddr, KnownEndpoint>,
    now: Instant,
) {
    known_endpoints.retain(|_, endpoint| {
        now.saturating_duration_since(endpoint.last_seen) <= PEERFINDER_LIVE_CACHE_TTL
    });
}

#[cfg(test)]
fn prune_recent_connect_attempts(
    recent_attempts: &mut HashMap<std::net::IpAddr, Instant>,
    now: Instant,
) {
    recent_attempts.retain(|_, until| *until > now);
}

#[cfg(test)]
fn peerfinder_canonical_ip(ip: std::net::IpAddr) -> std::net::IpAddr {
    match ip {
        std::net::IpAddr::V6(ipv6) => ipv6
            .to_ipv4_mapped()
            .map(std::net::IpAddr::V4)
            .unwrap_or(std::net::IpAddr::V6(ipv6)),
        std::net::IpAddr::V4(_) => ip,
    }
}

#[cfg(test)]
fn build_endpoint_broadcast(
    listening_port: Option<u16>,
    known_endpoints: &HashMap<std::net::SocketAddr, KnownEndpoint>,
    peer: &Arc<dyn overlay::Peer>,
    now: Instant,
) -> Vec<overlay::message::wire::tm_endpoints::TmEndpointv2> {
    let mut endpoints = Vec::with_capacity(PEERFINDER_NUMBER_OF_ENDPOINTS);

    // Match reference sendEndpoints shape more closely:
    // - advertise ourselves once at hops=0 when we want incoming peers,
    // - then hand out a bounded selection from the discovered live cache.
    if let Some(port) = listening_port {
        endpoints.push(overlay::message::wire::tm_endpoints::TmEndpointv2 {
            endpoint: std::net::SocketAddr::new(std::net::Ipv6Addr::UNSPECIFIED.into(), port)
                .to_string(),
            hops: 0,
        });
    }

    let mut discovered = known_endpoints
        .iter()
        .filter_map(|(addr, endpoint)| {
            (endpoint.hops > 0 && endpoint.hops <= PEERFINDER_MAX_HOPS + 1)
                .then_some((*addr, *endpoint))
        })
        .collect::<Vec<_>>();
    discovered.sort_by(|(left_addr, left), (right_addr, right)| {
        left.hops
            .cmp(&right.hops)
            .then_with(|| right.last_seen.cmp(&left.last_seen))
            .then_with(|| left_addr.cmp(right_addr))
    });

    let mut seen_ips = HashSet::new();
    for (addr, endpoint) in discovered {
        if endpoints.len() >= PEERFINDER_NUMBER_OF_ENDPOINTS {
            break;
        }
        if peerfinder_canonical_ip(peer.remote_address().ip()) == peerfinder_canonical_ip(addr.ip())
        {
            continue;
        }
        if peer.should_filter_recent_endpoint(addr, endpoint.hops, now, PEERFINDER_LIVE_CACHE_TTL) {
            continue;
        }
        if !seen_ips.insert(peerfinder_canonical_ip(addr.ip())) {
            continue;
        }
        peer.remember_recent_endpoint(addr, endpoint.hops, now, PEERFINDER_LIVE_CACHE_TTL);
        endpoints.push(overlay::message::wire::tm_endpoints::TmEndpointv2 {
            endpoint: addr.to_string(),
            hops: endpoint.hops,
        });
    }

    endpoints
}

#[cfg(test)]
fn select_autoconnect_endpoints(
    connected_ips: &std::collections::HashSet<std::net::IpAddr>,
    known_endpoints: &HashMap<std::net::SocketAddr, KnownEndpoint>,
    recent_attempts: &HashMap<std::net::IpAddr, Instant>,
    now: Instant,
) -> Vec<std::net::SocketAddr> {
    let mut candidates = known_endpoints
        .iter()
        .filter_map(|(addr, endpoint)| {
            (endpoint.hops <= PEERFINDER_MAX_HOPS
                && recent_attempts
                    .get(&peerfinder_canonical_ip(addr.ip()))
                    .is_none_or(|until| *until <= now))
            .then_some((*addr, *endpoint))
        })
        .collect::<Vec<_>>();
    candidates.sort_by(|(left_addr, left), (right_addr, right)| {
        left.hops
            .cmp(&right.hops)
            .then_with(|| right.last_seen.cmp(&left.last_seen))
            .then_with(|| left_addr.cmp(right_addr))
    });

    let mut seen_ips = connected_ips.clone();
    let mut selected = Vec::new();
    for (addr, _) in candidates {
        if seen_ips.insert(peerfinder_canonical_ip(addr.ip())) {
            selected.push(addr);
        }
        if selected.len() >= PEERFINDER_MAX_CONNECT_ATTEMPTS {
            break;
        }
    }
    selected
}

#[cfg(test)]
fn select_bootcache_endpoints(
    connected_ips: &std::collections::HashSet<std::net::IpAddr>,
    bootcache: &BTreeMap<std::net::SocketAddr, i32>,
    recent_attempts: &HashMap<std::net::IpAddr, Instant>,
    now: Instant,
) -> Vec<std::net::SocketAddr> {
    let mut candidates = bootcache
        .iter()
        .map(|(addr, valence)| (*addr, *valence))
        .collect::<Vec<_>>();
    candidates.sort_by(|(left_addr, left), (right_addr, right)| {
        right
            .cmp(left)
            .then_with(|| left_addr.ip().cmp(&right_addr.ip()))
            .then_with(|| left_addr.port().cmp(&right_addr.port()))
    });

    let mut seen_ips = connected_ips.clone();
    let mut selected = Vec::new();
    for (addr, _) in candidates {
        if recent_attempts
            .get(&peerfinder_canonical_ip(addr.ip()))
            .is_some_and(|until| *until > now)
        {
            continue;
        }
        if seen_ips.insert(peerfinder_canonical_ip(addr.ip())) {
            selected.push(addr);
        }
        if selected.len() >= PEERFINDER_MAX_CONNECT_ATTEMPTS {
            break;
        }
    }
    selected
}

#[cfg(test)]
fn peerfinder_outbound_target(peer_limit: usize, want_incoming: bool) -> usize {
    if peer_limit == 0 {
        return 0;
    }
    if !want_incoming {
        return peer_limit;
    }
    let computed = ((peer_limit * PEERFINDER_OUT_PERCENT) + 50) / 100;
    peer_limit.min(computed.max(PEERFINDER_MIN_OUTBOUND))
}

/// Server-startup flags that consume the following argument. Keep this list
/// aligned with `parse_bootstrap_args`: top-level CLI parsing uses it only to
/// avoid treating a startup flag's value as an RPC subcommand.
const STARTUP_VALUE_FLAGS: &[&str] = &[
    "--conf",
    "-c",
    "--rpc-url",
    "--quorum",
    "--nodeid",
    "--force_ledger_present_range",
    "--ledger",
    "--ledgerfile",
    "--trap_tx_hash",
    "--rpc_ip",
    "--rpc_port",
    "--unittest",
    "-u",
    "--unittest-arg",
    "--unittest-jobs",
    "--io-threads",
    "--job-queue-threads",
];

/// Try to parse CLI subcommands. Returns Some(ExitCode) if a subcommand was
/// handled, None if the node should start normally.
/// Resolve the RPC URL: if user passed --url explicitly, use it.
/// Otherwise, try to parse the config file to find the HTTP admin port.
fn resolve_rpc_url(parsed: &quaxar_cli::Cli) -> String {
    // If user explicitly set --rpc-url (not the default), use it as-is
    if parsed.rpc_url != "http://127.0.0.1:5005" {
        return parsed.rpc_url.clone();
    }

    // Try to find config and extract the RPC port
    let conf_path = parsed.conf.as_deref().unwrap_or_else(|| {
        if std::path::Path::new("quaxar.cfg").exists() {
            "quaxar.cfg"
        } else {
            ""
        }
    });

    if !conf_path.is_empty()
        && let Ok(content) = std::fs::read_to_string(conf_path)
        && let Some(url) = parse_rpc_url_from_config(&content)
    {
        return url;
    }

    parsed.rpc_url.clone()
}

/// Parse config to find the first port with protocol = http
fn parse_rpc_url_from_config(content: &str) -> Option<String> {
    let mut in_port_section = false;
    let mut port: Option<u16> = None;
    let mut ip: Option<String> = None;
    let mut is_http = false;

    fn rpc_host(ip: Option<&str>) -> &str {
        match ip {
            Some("0.0.0.0") | None => "127.0.0.1",
            Some(h) => h,
        }
    }

    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('#') || trimmed.is_empty() {
            continue;
        }
        if trimmed.starts_with("[port_") {
            // Save previous section if it was HTTP
            if in_port_section
                && is_http
                && let Some(p) = port
            {
                let host = rpc_host(ip.as_deref());
                return Some(format!("http://{}:{}", host, p));
            }
            in_port_section = true;
            port = None;
            ip = None;
            is_http = false;
        } else if trimmed.starts_with('[') {
            if in_port_section
                && is_http
                && let Some(p) = port
            {
                let host = rpc_host(ip.as_deref());
                return Some(format!("http://{}:{}", host, p));
            }
            in_port_section = false;
        } else if in_port_section {
            if let Some(val) = trimmed.strip_prefix("port") {
                if let Some(val) = val.trim().strip_prefix('=') {
                    port = val.trim().parse().ok();
                }
            } else if let Some(val) = trimmed.strip_prefix("ip") {
                if let Some(val) = val.trim().strip_prefix('=') {
                    ip = Some(val.trim().to_string());
                }
            } else if let Some(val) = trimmed.strip_prefix("protocol")
                && let Some(val) = val.trim().strip_prefix('=')
            {
                is_http = val.trim().contains("http");
            }
        }
    }

    // Check last section
    if in_port_section
        && is_http
        && let Some(p) = port
    {
        let host = rpc_host(ip.as_deref());
        return Some(format!("http://{}:{}", host, p));
    }

    None
}

fn try_cli_subcommand() -> Option<ExitCode> {
    use clap::{CommandFactory, Parser, error::ErrorKind};

    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        let _ = quaxar_cli::Cli::command().print_help();
        println!();
        return Some(ExitCode::SUCCESS);
    }

    // Known subcommands
    let subcommands = [
        "status",
        "health",
        "peers",
        "sync-status",
        "rpc",
        "ping",
        "server-info",
        "server-state",
        "server-definitions",
        "ledger-closed",
        "ledger-current",
        "ledger-header",
        "fetch-info",
        "get-counts",
        "can-delete",
        "log-rotate",
        "random",
        "validator-info",
        "validator-list-sites",
        "unl-list",
        "consensus-info",
        "tx-reduce-relay",
        "db-stats",
        "log-level",
        "config",
        "doctor",
        "version",
        "validators",
        "amendments",
        "fee",
        "ledger",
        "ledger-audit",
        "account",
        "stop",
        "connect",
        "benchmark",
        "validator-keys",
        "cli",
        "help",
        "--help",
        "-h",
        "--version",
        "-V",
    ];

    let parsed = match quaxar_cli::Cli::try_parse() {
        Ok(parsed) => parsed,
        Err(err)
            if matches!(
                err.kind(),
                ErrorKind::DisplayHelp | ErrorKind::DisplayVersion
            ) =>
        {
            let _ = err.print();
            return Some(ExitCode::SUCCESS);
        }
        Err(err)
            if args
                .iter()
                .skip(1)
                .any(|arg| subcommands.contains(&arg.as_str())) =>
        {
            let _ = err.print();
            return Some(ExitCode::FAILURE);
        }
        Err(err)
            if matches!(
                err.kind(),
                ErrorKind::UnknownArgument | ErrorKind::InvalidSubcommand
            ) =>
        {
            if let Some(command) = first_command_like_arg(&args, STARTUP_VALUE_FLAGS) {
                print_unknown_command(command, &subcommands);
                return Some(ExitCode::FAILURE);
            }
            // No subcommand found — likely node startup flags (--start, --valid, etc.)
            // Fall through to the node startup path where parse_bootstrap_args handles them.
            return None;
        }
        Err(err) => {
            let _ = err.print();
            return Some(ExitCode::FAILURE);
        }
    };
    let url = resolve_rpc_url(&parsed);
    let url = url.as_str();
    let cmd = parsed.command?;

    let ok = match cmd {
        quaxar_cli::Command::Status => quaxar_cli::status::run(url),
        quaxar_cli::Command::Health => {
            if !quaxar_cli::health::run(url) {
                return Some(ExitCode::FAILURE);
            }
            true
        }
        quaxar_cli::Command::Peers => quaxar_cli::peers::run(url),
        quaxar_cli::Command::SyncStatus => quaxar_cli::sync_status::run(url),
        quaxar_cli::Command::Rpc {
            method,
            params,
            raw,
        } => quaxar_cli::rpc_cmd::run(url, &method, params.as_deref(), raw),
        quaxar_cli::Command::Ping => quaxar_cli::rpc_cmd::run_no_params(url, "ping"),
        quaxar_cli::Command::ServerInfo => quaxar_cli::rpc_cmd::run_no_params(url, "server_info"),
        quaxar_cli::Command::ServerState => quaxar_cli::rpc_cmd::run_no_params(url, "server_state"),
        quaxar_cli::Command::ServerDefinitions => {
            quaxar_cli::rpc_cmd::run_no_params(url, "server_definitions")
        }
        quaxar_cli::Command::LedgerClosed => {
            quaxar_cli::rpc_cmd::run_no_params(url, "ledger_closed")
        }
        quaxar_cli::Command::LedgerCurrent => {
            quaxar_cli::rpc_cmd::run_no_params(url, "ledger_current")
        }
        quaxar_cli::Command::LedgerHeader => {
            quaxar_cli::rpc_cmd::run_no_params(url, "ledger_header")
        }
        quaxar_cli::Command::FetchInfo => quaxar_cli::rpc_cmd::run_no_params(url, "fetch_info"),
        quaxar_cli::Command::GetCounts => quaxar_cli::rpc_cmd::run_no_params(url, "get_counts"),
        quaxar_cli::Command::CanDelete { value } => {
            quaxar_cli::rpc_cmd::run_can_delete(url, value.as_deref())
        }
        quaxar_cli::Command::LogRotate => quaxar_cli::rpc_cmd::run_logrotate(url),
        quaxar_cli::Command::Random => quaxar_cli::rpc_cmd::run_no_params(url, "random"),
        quaxar_cli::Command::ValidatorInfo => {
            quaxar_cli::rpc_cmd::run_no_params(url, "validator_info")
        }
        quaxar_cli::Command::ValidatorListSites => {
            quaxar_cli::rpc_cmd::run_no_params(url, "validator_list_sites")
        }
        quaxar_cli::Command::UnlList => quaxar_cli::rpc_cmd::run_no_params(url, "unl_list"),
        quaxar_cli::Command::ConsensusInfo => {
            quaxar_cli::rpc_cmd::run_no_params(url, "consensus_info")
        }
        quaxar_cli::Command::TxReduceRelay => {
            quaxar_cli::rpc_cmd::run_no_params(url, "tx_reduce_relay")
        }
        quaxar_cli::Command::DbStats => quaxar_cli::db_stats::run(url, parsed.conf.as_deref()),
        quaxar_cli::Command::LogLevel { level } => {
            quaxar_cli::log_level::run(url, level.as_deref())
        }
        quaxar_cli::Command::ConfigCheck => {
            quaxar_cli::config_check::run(parsed.conf.as_deref());
            true
        }
        quaxar_cli::Command::Doctor => {
            quaxar_cli::doctor::run(url, parsed.conf.as_deref());
            true
        }
        quaxar_cli::Command::Version => {
            quaxar_cli::version::run();
            true
        }
        quaxar_cli::Command::Validators => quaxar_cli::validators::run(url),
        quaxar_cli::Command::Amendments => quaxar_cli::amendments::run(url),
        quaxar_cli::Command::Fee => quaxar_cli::fee::run(url),
        quaxar_cli::Command::Ledger { seq } => quaxar_cli::ledger_cmd::run(url, seq),
        quaxar_cli::Command::LedgerAudit {
            network,
            ledger,
            output,
            source_url,
        } => quaxar_cli::ledger_audit::run(&network, &ledger, &output, source_url.as_deref()),
        quaxar_cli::Command::Account { address } => quaxar_cli::account::run(url, &address),
        quaxar_cli::Command::Stop => quaxar_cli::stop::run(url),
        quaxar_cli::Command::Connect { address } => {
            let result = quaxar_cli::rpc_call(url, "connect", serde_json::json!({"ip": address}));
            match result {
                Ok(_) => {
                    println!(
                        "  {} Connect request sent to {}",
                        console::Style::new().green().apply_to("●"),
                        address
                    );
                    true
                }
                Err(e) => {
                    eprintln!("  {} {}", console::Style::new().red().apply_to("●"), e);
                    false
                }
            }
        }
        quaxar_cli::Command::Benchmark => {
            quaxar_cli::benchmark::run();
            true
        }
        quaxar_cli::Command::Cli => {
            quaxar_cli::interactive::run(url);
            true
        }
        quaxar_cli::Command::ValidatorKeys { action } => {
            use quaxar_cli::ValidatorKeysAction;
            match action {
                ValidatorKeysAction::Generate => quaxar_cli::validator_keys::run_generate(),
                ValidatorKeysAction::CreateToken { secret } => {
                    quaxar_cli::validator_keys::run_create_token(secret.as_deref())
                }
                ValidatorKeysAction::Sign { data } => quaxar_cli::validator_keys::run_sign(&data),
                ValidatorKeysAction::Revoke => quaxar_cli::validator_keys::run_revoke(),
                ValidatorKeysAction::Show => quaxar_cli::validator_keys::run_show(),
            }
            true
        }
        quaxar_cli::Command::ExportSnapshot { output } => run_export_snapshot(url, &output),
        quaxar_cli::Command::LoadSnapshot { input } => {
            run_load_snapshot(&input, parsed.conf.as_deref())
        }
    };
    Some(if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    })
}

fn first_command_like_arg<'a>(args: &'a [String], value_flags: &[&str]) -> Option<&'a str> {
    let mut index = 1;
    while index < args.len() {
        let arg = args[index].as_str();
        if value_flags.contains(&arg) {
            index += 2;
            continue;
        }
        if arg.starts_with("--conf=") || arg.starts_with("--rpc-url=") {
            index += 1;
            continue;
        }
        if arg.starts_with('-') {
            index += 1;
            continue;
        }
        return Some(arg);
    }
    None
}

fn print_unknown_command(command: &str, subcommands: &[&str]) {
    eprintln!(
        "  {} Unknown command: {command}",
        console::Style::new().red().apply_to("●")
    );

    let suggestions = command_suggestions(command, subcommands);
    if !suggestions.is_empty() {
        eprintln!(
            "    Did you mean {}?",
            suggestions
                .iter()
                .map(|suggestion| format!("`{suggestion}`"))
                .collect::<Vec<_>>()
                .join(" or ")
        );
    }

    eprintln!("    Run `quaxar --help` to see available commands.");
}

fn command_suggestions<'a>(command: &str, subcommands: &'a [&str]) -> Vec<&'a str> {
    let normalized = command.to_ascii_lowercase();
    let singular = normalized.strip_suffix('s').unwrap_or(&normalized);
    let mut suggestions = subcommands
        .iter()
        .copied()
        .filter(|candidate| {
            let candidate = candidate.to_ascii_lowercase();
            candidate.starts_with(singular)
                || candidate.contains(singular)
                || levenshtein_distance(&normalized, &candidate) <= 3
        })
        .take(3)
        .collect::<Vec<_>>();
    suggestions.sort_unstable();
    suggestions.dedup();
    suggestions
}

fn levenshtein_distance(left: &str, right: &str) -> usize {
    let mut previous = (0..=right.len()).collect::<Vec<_>>();
    let mut current = vec![0; right.len() + 1];

    for (left_index, left_char) in left.chars().enumerate() {
        current[0] = left_index + 1;
        for (right_index, right_char) in right.chars().enumerate() {
            let substitution = previous[right_index] + usize::from(left_char != right_char);
            let insertion = current[right_index] + 1;
            let deletion = previous[right_index + 1] + 1;
            current[right_index + 1] = substitution.min(insertion).min(deletion);
        }
        std::mem::swap(&mut previous, &mut current);
    }

    previous[right.len()]
}

fn main() -> ExitCode {
    // Initialize structured logging
    // Check for CLI subcommands first (status, health, peers, etc.)
    // If a subcommand is present, run it and exit without starting the node.
    if let Some(exit) = try_cli_subcommand() {
        return exit;
    }

    use tracing_subscriber::prelude::*;

    let filter = tracing_subscriber::EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| tracing_subscriber::EnvFilter::new("info"));
    let (filter_layer, reload_handle) = tracing_subscriber::reload::Layer::new(filter);

    let subscriber = tracing_subscriber::registry().with(filter_layer).with(
        tracing_subscriber::fmt::layer()
            .with_target(true)
            .with_thread_ids(true),
    );
    tracing::subscriber::set_global_default(subscriber).expect("setting default subscriber");

    app::set_log_reload_fn(move |new_filter: &str| {
        let f = tracing_subscriber::EnvFilter::try_new(new_filter)
            .map_err(|e| format!("Invalid filter: {e}"))?;
        reload_handle
            .reload(f)
            .map_err(|e| format!("Reload failed: {e}"))
    });

    tracing::info!(target: "main", version = env!("CARGO_PKG_VERSION"), "QUAXAR starting");

    // rippled starts its cached uptime clock on first use during normal app
    // initialization. Prime it before potentially long bootstrap work so RPC
    // uptime is the node process lifetime, not time since the first RPC call.
    let _ = UptimeClock::now();
    let start_time = Instant::now();

    let args: Vec<String> = std::env::args().collect();
    let options = match parse_bootstrap_args(args) {
        Ok(options) => options,
        Err(error) => {
            tracing::error!(target: "main", %error, "Fatal error — shutting down");
            return ExitCode::from(1);
        }
    };

    if !options.rpc_parameters.is_empty() {
        return run_rpc_client(options);
    }

    // Server mode
    let config_path = options.config_path.clone();
    tracing::info!(target: "main", config_path = %config_path.display(), "Configuration loaded");

    // Spin up a Tokio runtime wrapper for async contexts needed during build
    let rt = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap();
    let _guard = rt.enter();

    let bootstrap = match build_composed_runtime_from_path(config_path, options) {
        Ok(bootstrap) => {
            tracing::info!(target: "main", "Database opened");
            bootstrap
        }
        Err(error) => {
            tracing::error!(target: "main", %error, "Fatal error — shutting down");
            return ExitCode::from(1);
        }
    };

    tracing::info!(target: "main", "Node fully operational");

    match run_bootstrap_runtime(bootstrap) {
        Ok(()) => {
            let uptime_seconds = start_time.elapsed().as_secs();
            tracing::info!(target: "main", uptime_seconds, "Node stopped");
            ExitCode::SUCCESS
        }
        Err(error) => {
            let uptime_seconds = start_time.elapsed().as_secs();
            tracing::error!(target: "main", %error, "Fatal error — shutting down");
            tracing::info!(target: "main", uptime_seconds, "Node stopped");
            ExitCode::from(1)
        }
    }
}

#[derive(Clone)]
struct BoundServerRuntime<D> {
    runtime: ServerRuntime<D>,
    handler: Arc<app::AppServerHandler>,
    app: app::ApplicationRoot,
    catch_up_state: Arc<CatchUpState>,
}

#[cfg(test)]
fn select_target_seq(
    validated: u32,
    has_shared_range: bool,
    selection_ceiling: u32,
    quorum_target_seq: Option<u32>,
) -> u32 {
    if selection_ceiling <= validated {
        return 0;
    }

    // ledger (from incoming validations) over the shared tip. This ensures we
    // acquire the ledger that has quorum, not the most recent tip which may
    // not have enough validations yet and which fewer peers may have state for.
    if validated <= 1 {
        if let Some(seq) = quorum_target_seq
            && seq > 1
            && seq <= selection_ceiling
        {
            return seq;
        }
        if has_shared_range {
            return selection_ceiling.max(2);
        }
    }

    let next_seq = validated.saturating_add(1).max(2);
    if next_seq > selection_ceiling {
        return 0;
    }

    // When we can get the hash for validated+1 (from skip list or history),
    // walk sequentially — this is the reference findNewLedgersToPublish path.
    // When we can't (e.g. after GapTooLarge, validated+1 is a future ledger
    // with no known hash), use the quorum target which has a live hash from
    // incoming validations. This lets the node keep jumping toward the tip.
    if let Some(seq) = quorum_target_seq
        && seq > next_seq
        && seq <= selection_ceiling
    {
        return seq;
    }

    next_seq
}

#[cfg(test)]
fn select_consensus_acquisition_target(
    validated: u32,
    validated_hash_targets: &[(Uint256, u32)],
) -> Option<(Uint256, u32)> {
    let gap = validated_hash_targets
        .iter()
        .map(|(_, seq)| *seq)
        .min()
        .unwrap_or(0)
        .saturating_sub(validated);

    if validated <= 1 {
        // Cold bootstrap needs one current quorum-backed anchor. reference does not
        // spawn an inbound ledger for every observed validation hash; missing
        // consensus ledgers are requested through the preferred-ledger path and
        // deduplicated by hash inside InboundLedgers.
        validated_hash_targets
            .iter()
            .max_by_key(|(_, seq)| *seq)
            .copied()
    } else if gap <= 5 {
        // Near the validated stream, prefer the closest missing ledger so
        // publishing can advance sequentially.
        validated_hash_targets
            .iter()
            .min_by_key(|(_, seq)| *seq)
            .copied()
    } else {
        // Large catchup gaps use the freshest trusted consensus ledger as the
        // bootstrap/reference target.
        validated_hash_targets.last().copied()
    }
}

#[cfg(test)]
fn cold_bootstrap_persisted_validated_target(
    validated: u32,
    last_validated_target: Option<(Uint256, u32)>,
) -> Option<(Uint256, u32)> {
    let _ = (validated, last_validated_target);
    None
}

#[cfg(test)]
fn hash_for_seq_from_reference_ledger(
    reference_ledger: &ledger::Ledger,
    target_seq: u32,
) -> Option<basics::sha_map_hash::SHAMapHash> {
    if target_seq == 0 || reference_ledger.header().seq < target_seq {
        return None;
    }

    if reference_ledger.header().seq == target_seq {
        return Some(reference_ledger.header().hash);
    }

    reference_ledger
        .hash_of_seq(target_seq, &ledger::NullLedgerJournal)
        .filter(|hash| !hash.is_zero())
}

#[cfg(test)]
fn candidate_ledger_for_seq(target_seq: u32) -> u32 {
    target_seq.saturating_add(255) & !255
}

#[cfg(test)]
fn candidate_reference_hash_from_reference_ledger(
    reference_ledger: &ledger::Ledger,
    target_seq: u32,
) -> Option<(u32, basics::sha_map_hash::SHAMapHash)> {
    if target_seq == 0 || reference_ledger.header().seq < target_seq {
        return None;
    }

    if hash_for_seq_from_reference_ledger(reference_ledger, target_seq).is_some() {
        return None;
    }

    let candidate_seq = candidate_ledger_for_seq(target_seq);
    if candidate_seq <= target_seq || reference_ledger.header().seq < candidate_seq {
        return None;
    }

    reference_ledger
        .hash_of_seq(candidate_seq, &ledger::NullLedgerJournal)
        .filter(|hash| !hash.is_zero())
        .map(|hash| (candidate_seq, hash))
}

#[cfg(test)]
fn promote_current_ledger(
    app: &app::ApplicationRoot,
    peers: &[Arc<dyn overlay::Peer>],
    ledger: std::sync::Arc<ledger::Ledger>,
) {
    if let Some(lm_rt) = app.ledger_master_runtime() {
        // Rust currently has both the app-owned published/current holder and
        // the app-runtime LedgerMaster published holder. reference has one
        // LedgerMaster owner, so keep both Rust holders aligned here whenever
        // the accepted ledger becomes the app's current published ledger.
        lm_rt
            .ledger_master()
            .set_pub_ledger(std::sync::Arc::clone(&ledger));
    }
    app.on_closed_ledger(std::sync::Arc::clone(&ledger));
    app.note_validated_ledger_for_sync(std::sync::Arc::clone(&ledger));
    app.on_published_ledger(std::sync::Arc::clone(&ledger));
    // Only clear need_network_ledger if we have a real validated ledger (not genesis)
    if ledger.header().seq > 1 {
        app.set_need_network_ledger(false);
    } else {
        app.set_need_network_ledger(true);
    }

    let next_seq = ledger.header().seq.saturating_add(1);
    app.set_status_rpc_current_ledger_index(Some(next_seq));
    let base_fee = ledger.fees().base;
    let load_base = app.load_fee_track().load_base();
    let mut fees = app.validations().store().fees_for_ledger(
        *ledger.header().hash.as_uint256(),
        ledger.header().seq,
        load_base,
    );
    if !fees.is_empty() {
        fees.sort();
        let median = fees[fees.len() / 2];
        app.load_fee_track().set_remote_fee(median);
    }
    let parent_hash = *ledger.header().hash.as_uint256();
    let _ = app.open_ledger().modify(|view| {
        *view = app::AppOpenLedgerView::with_parent_timing(
            next_seq,
            base_fee,
            parent_hash,
            ledger.header().close_time,
            ledger.header().close_time_resolution,
        );
        true
    });

    if let Some(lm_rt) = app.ledger_master_runtime() {
        let complete = lm_rt.ledger_master().complete_ledgers();
        if !complete.empty() {
            app.set_status_rpc_complete_ledgers(Some(complete.to_string()));
        }
    }

    let hdr = ledger.header();
    let status_msg = overlay::ProtocolMessage::new(overlay::ProtocolPayload::StatusChange(
        overlay::message::wire::TmStatusChange {
            new_status: Some(1),
            new_event: Some(1),
            ledger_seq: Some(hdr.seq),
            ledger_hash: Some(hdr.hash.as_uint256().data().to_vec()),
            ledger_hash_previous: Some(hdr.parent_hash.as_uint256().data().to_vec()),
            network_time: None,
            first_seq: app.ledger_master_runtime().map(|lm| {
                let cl = lm.ledger_master().complete_ledgers();
                cl.first().unwrap_or(0)
            }),
            last_seq: app.ledger_master_runtime().map(|lm| {
                let cl = lm.ledger_master().complete_ledgers();
                cl.last().unwrap_or(0)
            }),
        },
    ));
    let wire = overlay::Message::new(status_msg, None);
    for peer in peers {
        peer.send(wire.clone());
    }
    update_operating_mode_after_accepted_ledger(app, peers, ledger.as_ref());
}

// Kept for compatibility with LedgerMaster publish-gap classification; the
// current Rust runtime does not route this helper through the active bin path.
#[cfg(test)]
const MAX_LEDGER_GAP_TO_PUBLISH_SEQUENTIALLY: u32 = 100;

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LedgerPublishAdvance {
    FirstPublished,
    GapTooLarge,
    Sequential,
    NothingToPublish,
}

#[cfg(test)]
fn classify_publish_advance(valid_seq: u32, published_seq: Option<u32>) -> LedgerPublishAdvance {
    let Some(published_seq) = published_seq else {
        return LedgerPublishAdvance::FirstPublished;
    };
    if valid_seq > published_seq.saturating_add(MAX_LEDGER_GAP_TO_PUBLISH_SEQUENTIALLY) {
        return LedgerPublishAdvance::GapTooLarge;
    }
    if valid_seq <= published_seq {
        return LedgerPublishAdvance::NothingToPublish;
    }
    LedgerPublishAdvance::Sequential
}

#[cfg(test)]
fn should_retry_publish_after_completed_history(
    acquired_seq: u32,
    published_seq: Option<u32>,
    valid_seq: u32,
) -> bool {
    let Some(published_seq) = published_seq else {
        return false;
    };
    acquired_seq > published_seq && acquired_seq <= valid_seq
}

// After inserting acquired ledgers into history, walk pub_seq+1 → val_seq
// sequentially. For each seq, look up the ledger in history by hash (using
// the validated ledger's skip list), then build it using the previous ledger
// as parent. This guarantees the parent is always available before the child
// is built — exactly how reference processes ledgers.
//
// Pure acquire-and-trust path was here (try_advance_catchup and
// try_promote_ledger_with_validations) — deleted: these were remnants of the
// legacy catchup loop and are not used by the NetworkOpsStrand runtime.

#[cfg(test)]
fn should_attempt_completed_ledger_promotion(
    acquired_seq: u32,
    current_validated_seq: u32,
) -> bool {
    // behind validLedgerSeq_. They are useful history, not promotion candidates.
    acquired_seq > current_validated_seq
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CompletedLedgerAcceptance {
    HistoricalCached,
    HeldForQuorum,
    ValidatedAccepted,
}

#[cfg(test)]
#[allow(dead_code)] // exercised by M7 sweep; kept for lifecycle/promotion tests
impl CompletedLedgerAcceptance {
    fn log_label(self) -> &'static str {
        match self {
            Self::HistoricalCached => "historical_cached",
            Self::HeldForQuorum => "held_for_quorum",
            Self::ValidatedAccepted => "validated_accepted",
        }
    }

    fn promotes_validated_ledger(self) -> bool {
        matches!(self, Self::ValidatedAccepted)
    }
}

#[cfg(test)]
fn classify_completed_ledger_acceptance(
    acquired_seq: u32,
    current_validated_seq: u32,
    is_skip_state: bool,
    check_accept_passed: bool,
) -> CompletedLedgerAcceptance {
    let _ = is_skip_state;
    if !should_attempt_completed_ledger_promotion(acquired_seq, current_validated_seq) {
        return CompletedLedgerAcceptance::HistoricalCached;
    }
    if check_accept_passed {
        return CompletedLedgerAcceptance::ValidatedAccepted;
    }
    CompletedLedgerAcceptance::HeldForQuorum
}

#[cfg(test)]
fn preferred_closed_ledger_hash_from_hashes(
    peer_hashes: impl IntoIterator<Item = Uint256>,
    our_closed_hash: Uint256,
    count_our_closed: bool,
) -> Option<Uint256> {
    let mut peer_counts = HashMap::<Uint256, u32>::new();
    if count_our_closed {
        peer_counts.insert(our_closed_hash, 1);
    }

    for hash in peer_hashes {
        if !hash.is_zero() {
            *peer_counts.entry(hash).or_insert(0) += 1;
        }
    }

    peer_counts
        .into_iter()
        .max_by(|(hash_a, count_a), (hash_b, count_b)| {
            count_a.cmp(count_b).then_with(|| hash_a.cmp(hash_b))
        })
        .map(|(hash, _)| hash)
}

#[cfg(test)]
fn preferred_closed_ledger_hash(
    trusted_preferred: Option<(u32, Uint256)>,
    min_valid_seq: u32,
    peer_hashes: impl IntoIterator<Item = Uint256>,
    our_closed_hash: Uint256,
    prev_closed_hash: Uint256,
    count_our_closed: bool,
) -> Uint256 {
    let preferred = trusted_preferred
        .map(|(seq, hash)| {
            if seq >= min_valid_seq {
                hash
            } else {
                our_closed_hash
            }
        })
        .or_else(|| {
            preferred_closed_ledger_hash_from_hashes(peer_hashes, our_closed_hash, count_our_closed)
        })
        .unwrap_or(our_closed_hash);

    if preferred != our_closed_hash && preferred == prev_closed_hash {
        return our_closed_hash;
    }

    preferred
}

#[cfg(test)]
fn peer_prefers_different_closed_ledger(
    app: &app::ApplicationRoot,
    peers: &[Arc<dyn overlay::Peer>],
    accepted_ledger: &ledger::Ledger,
    count_our_closed: bool,
) -> bool {
    let our_closed_hash = *accepted_ledger.header().hash.as_uint256();
    let trusted_preferred = app
        .validations()
        .validations()
        .lock()
        .expect("validations lock should not be poisoned")
        .get_preferred(&app::validated_ledger_from_ledger(
            accepted_ledger,
            &app::NullRclValidationJournal,
        ));

    let preferred = preferred_closed_ledger_hash(
        trusted_preferred,
        app.validated_ledger_seq().unwrap_or(0),
        peers.iter().map(|peer| peer.closed_ledger_hash()),
        our_closed_hash,
        *accepted_ledger.header().parent_hash.as_uint256(),
        count_our_closed,
    );

    preferred != our_closed_hash
}

#[cfg(test)]
fn current_ledger_is_fresh(
    now_close_time: u32,
    last_closed_close_time: u32,
    close_time_resolution: u32,
) -> bool {
    now_close_time < last_closed_close_time.saturating_add(close_time_resolution.saturating_mul(2))
}

#[cfg(test)]
fn select_post_acquisition_operating_mode(
    current_mode: app::NetworkOpsOperatingMode,
    need_network_ledger: bool,
    ledger_change: bool,
    current_ledger_fresh: bool,
) -> app::NetworkOpsOperatingMode {
    let mut next_mode = current_mode;

    if matches!(
        next_mode,
        app::NetworkOpsOperatingMode::Connected | app::NetworkOpsOperatingMode::Syncing
    ) && !need_network_ledger
        && !ledger_change
    {
        next_mode = app::NetworkOpsOperatingMode::Tracking;
    }

    if matches!(
        next_mode,
        app::NetworkOpsOperatingMode::Connected | app::NetworkOpsOperatingMode::Tracking
    ) && !need_network_ledger
        && !ledger_change
        && current_ledger_fresh
    {
        next_mode = app::NetworkOpsOperatingMode::Full;
    }

    next_mode
}

#[cfg(test)]
fn update_operating_mode_after_accepted_ledger(
    app: &app::ApplicationRoot,
    peers: &[Arc<dyn overlay::Peer>],
    accepted_ledger: &ledger::Ledger,
) {
    let current_mode = app.network_ops_operating_mode();
    let ledger_change = peer_prefers_different_closed_ledger(
        app,
        peers,
        accepted_ledger,
        matches!(
            current_mode,
            app::NetworkOpsOperatingMode::Tracking | app::NetworkOpsOperatingMode::Full
        ),
    );

    // rippled: switchLastClosedLedger — when peers/validations prefer a
    // different ledger, JUMP to it. This is the critical recovery path that
    // prevents the node from getting stuck on a stale chain.
    if ledger_change && let Some(lm_rt) = app.ledger_master_runtime() {
        let our_closed_hash = *accepted_ledger.header().hash.as_uint256();
        let trusted_preferred = app
            .validations()
            .validations()
            .lock()
            .expect("validations lock")
            .get_preferred(&app::validated_ledger_from_ledger(
                accepted_ledger,
                &app::NullRclValidationJournal,
            ));
        let peer_hashes: Vec<Uint256> = peers.iter().map(|p| p.closed_ledger_hash()).collect();
        let preferred_hash = preferred_closed_ledger_hash(
            trusted_preferred,
            app.validated_ledger_seq().unwrap_or(0),
            peer_hashes,
            our_closed_hash,
            *accepted_ledger.header().parent_hash.as_uint256(),
            true,
        );

        if preferred_hash != our_closed_hash && !preferred_hash.is_zero() {
            // Try to get the preferred ledger from history or inbound
            let ledger_master = lm_rt.ledger_master();
            if let Some(target) = ledger_master
                .get_ledger_by_hash(basics::sha_map_hash::SHAMapHash::new(preferred_hash))
            {
                tracing::warn!(target: "consensus",
                    our_seq = accepted_ledger.header().seq,
                    target_seq = target.header().seq,
                    "JUMP: switchLastClosedLedger to peer-preferred ledger"
                );
                // Promote: set as valid if quorum is met
                let target_seq = target.header().seq;
                let validations = app
                    .validations()
                    .store()
                    .trusted_for_ledger_by_sequence(preferred_hash, target_seq);
                let val_count = app
                    .validators()
                    .negative_unl_filter_validations(validations)
                    .len();
                let quorum = app.validators().quorum();
                if val_count >= quorum {
                    let mut promoted = app.ledger_with_node_fetcher(std::sync::Arc::clone(&target));
                    {
                        let l = std::sync::Arc::make_mut(&mut promoted);
                        l.set_validated();
                        l.set_full();
                        l.finalize_immutable_no_setup();
                    }
                    ledger_master
                        .ledger_history()
                        .insert(std::sync::Arc::clone(&promoted), true);
                    ledger_master.mark_ledger_complete(target_seq);
                    ledger_master.set_valid_ledger_no_sweep(
                        std::sync::Arc::clone(&promoted),
                        None,
                        None,
                    );
                    app.note_validated_ledger_for_sync(std::sync::Arc::clone(&promoted));
                    app.set_need_network_ledger(false);
                    tracing::info!(target: "consensus",
                        seq = target_seq,
                        validations = val_count,
                        "JUMP: validated ledger promoted (switchLastClosedLedger)"
                    );
                } else {
                    tracing::debug!(target: "consensus",
                        seq = target_seq,
                        val_count,
                        quorum,
                        "JUMP: preferred ledger acquired but quorum not met yet"
                    );
                }
            } else {
                // Don't have it — request acquisition (non-blocking)
                tracing::info!(target: "consensus",
                    hash = %format!("{:016x}", preferred_hash.data()[0] as u64),
                    "JUMP: requesting preferred ledger acquisition"
                );
            }
        }
    }

    let next_mode = select_post_acquisition_operating_mode(
        current_mode,
        app.need_network_ledger(),
        ledger_change,
        current_ledger_is_fresh(
            app.current_close_time_seconds(),
            accepted_ledger.header().close_time,
            u32::from(accepted_ledger.header().close_time_resolution),
        ),
    );

    if next_mode != current_mode {
        let _ = app.set_network_ops_operating_mode(next_mode);
    }
}

#[cfg(test)]
fn node_store_usage_path(config: &BasicConfig) -> Option<PathBuf> {
    let path = config
        .section("node_db")
        .get::<String>("path")
        .ok()
        .flatten()?;
    Some(PathBuf::from(path))
}

#[cfg(test)]
fn path_size_bytes(path: &Path) -> u64 {
    let mut total = 0_u64;
    let mut stack = vec![path.to_path_buf()];

    while let Some(next) = stack.pop() {
        let Ok(metadata) = std::fs::metadata(&next) else {
            continue;
        };

        if metadata.is_file() {
            total = total.saturating_add(metadata.len());
            continue;
        }

        if metadata.is_dir() {
            let Ok(entries) = std::fs::read_dir(&next) else {
                continue;
            };
            stack.extend(entries.filter_map(|entry| entry.ok().map(|entry| entry.path())));
        }
    }

    total
}

impl<D> BoundServerRuntime<D> {
    fn new(
        runtime: ServerRuntime<D>,
        handler: Arc<app::AppServerHandler>,
        app: app::ApplicationRoot,
    ) -> Self {
        Self {
            runtime,
            handler,
            app,
            catch_up_state: Arc::new(CatchUpState::default()),
        }
    }

    fn start_catch_up_loop(&self) {
        // All ledger acquisition, consensus, acceptance, history backfill,
        // and overlay service duties are now handled by the NetworkOpsStrand
        // spawned during bootstrap. This method is retained as a no-op for
        // API compatibility with BoundServerRuntime's ManagedComponent impl.
        tracing::info!(target: "main", "Ledger catch-up delegated to NetworkOpsStrand (no legacy loop)");
    }

    fn stop_catch_up_loop(&self) {
        tracing::info!(target: "main", "Shutdown signal received");
        self.catch_up_state.stop.store(true, Ordering::Release);
        self.app.job_queue().stop();
    }
}

#[derive(Default)]
struct CatchUpState {
    stop: AtomicBool,
}

impl<D> ManagedComponent for BoundServerRuntime<D>
where
    D: server::RpcDispatcher + Clone + Send + Sync + 'static,
{
    fn start(&self) -> Result<(), String> {
        self.runtime.start()?;
        self.start_catch_up_loop();
        self.handler.mark_started(true);
        Ok(())
    }

    fn stop(&self) {
        self.stop_catch_up_loop();
        self.runtime.stop();
        self.handler.mark_started(false);
    }

    fn fd_required(&self) -> usize {
        self.runtime.fd_required()
    }
}

fn build_composed_runtime_from_path(
    path: impl AsRef<std::path::Path>,
    mut options: AppBootstrapOptions,
) -> Result<AppBootstrapRuntime, String> {
    options.config_path = path.as_ref().to_path_buf();
    let config = load_basic_config_file(&options.config_path)?;
    let bootstrap = build_bootstrap_root(&config, &options)?;
    let mut report = bootstrap.report;
    let mut root = bootstrap.root;

    if let Ok(server_build) = ServerRuntime::from_application_root_with_report(&root) {
        if let Some(overlay_runtime) = root.overlay_runtime() {
            let subscriptions = server_build.runtime.subscriptions();
            let subs_clone = subscriptions.clone();
            root.set_ledger_delta_publisher(move |payload| {
                subs_clone.publish_json(server::StreamKind::LedgerDelta, payload);
            });
            overlay_runtime
                .overlay()
                .set_peer_status_publisher(move |payload| {
                    subscriptions.publish_json(server::StreamKind::PeerStatus, payload);
                });

            // Overlay peer listener: inbound connections are accepted when
            // the overlay has a TLS acceptor configured. The overlay's
            // run_listener is spawned by the overlay runtime itself when
            // a TcpListener is provided via overlay.bind().
            // Production binding happens through the app's overlay_runtime
            // configuration which sets up the peer port from [port_peer].
            tracing::info!(target: "main", "Overlay started — connecting to peers");
        }
        let peer_port = report
            .server_configured_ports
            .iter()
            .find(|p| p.contains("peer"))
            .map(|s| s.as_str())
            .unwrap_or("none");
        let rpc_port = report
            .server_configured_ports
            .iter()
            .find(|p| p.contains("rpc"))
            .map(|s| s.as_str())
            .unwrap_or("none");
        let ws_port = report
            .server_configured_ports
            .iter()
            .find(|p| p.contains("ws"))
            .map(|s| s.as_str())
            .unwrap_or("none");
        tracing::info!(target: "main", peer_port, rpc_port, ws_port, "Ports configured");
        bind_server_runtime_into_root(&mut root, &mut report, server_build);
    }

    Ok(AppBootstrapRuntime {
        runtime: Arc::new(MainRuntime::new(root)),
        sweep_interval_seconds: report.sweep_interval_seconds,
        report,
    })
}

fn bind_server_runtime_into_root<D>(
    root: &mut app::ApplicationRoot,
    report: &mut app::AppBootstrapReport,
    server_build: ServerRuntimeBuildReport<D>,
) where
    D: server::RpcDispatcher + Clone + Send + Sync + 'static,
{
    let handler = root.server_handler();
    let app_for_runtime = root.clone();
    let configured_ports: Vec<String> = root
        .server_ports_setup()
        .map(|setup| setup.ports.iter().map(|port| port.name.clone()).collect())
        .unwrap_or_default();
    let deferred_protocols = server_build
        .deferred_protocols
        .iter()
        .map(|protocol| format!("{} on {}", protocol.protocol, protocol.port_name))
        .collect::<Vec<_>>();
    handler.configure(configured_ports.clone(), deferred_protocols.clone());
    let runtime = Arc::new(BoundServerRuntime::new(
        server_build.runtime,
        handler,
        app_for_runtime,
    ));
    let _ = root.bind_server(runtime);
    report.has_server_runtime = true;
    report.server_configured_ports = configured_ports;
    report.deferred_protocols = deferred_protocols;
    report.fd_required = root.fd_required();
}

fn run_rpc_client(options: AppBootstrapOptions) -> ExitCode {
    let config = match load_basic_config_file(&options.config_path) {
        Ok(config) => config,
        Err(error) => {
            tracing::error!(target: "main", %error, "Configuration error");
            return ExitCode::from(1);
        }
    };

    // Determine RPC endpoint
    let rpc_ip = options.rpc_ip.unwrap_or_else(|| {
        config
            .legacy("rpc_ip")
            .ok()
            .filter(|s| !s.is_empty())
            .unwrap_or_else(|| "127.0.0.1".to_string())
    });
    let rpc_port = options.rpc_port.unwrap_or_else(|| {
        config
            .legacy("rpc_port")
            .ok()
            .and_then(|s| s.parse::<u16>().ok())
            .unwrap_or(5005)
    });

    let request_json = match rpc_cmd_to_json(&options.rpc_parameters, 1) {
        Ok(json) => json,
        Err(status) => {
            tracing::error!(target: "main", message = status.message(), "RPC command error");
            return ExitCode::from(1);
        }
    };

    let client = reqwest::blocking::Client::new();
    let url = format!("http://{}:{}/", rpc_ip, rpc_port);

    let body = serde_json::to_string(&request_json).unwrap();

    match client
        .post(&url)
        .header("Content-Type", "application/json")
        .body(body)
        .send()
    {
        Ok(response) => {
            let status = response.status();
            let text = response.text().unwrap_or_default();
            if status.is_success() {
                println!("{}", text);
                ExitCode::SUCCESS
            } else {
                tracing::error!(target: "main", %status, text, "RPC server error");
                ExitCode::from(1)
            }
        }
        Err(error) => {
            tracing::error!(target: "main", %error, "Failed to connect to RPC server");
            ExitCode::from(1)
        }
    }
}

#[cfg(test)]
#[path = "main/tests.rs"]
mod tests;

// ─── Snapshot CLI handlers ───────────────────────────────────────────────────

fn snapshot_spinner(message: impl Into<String>) -> ProgressBar {
    let spinner = ProgressBar::new_spinner();
    spinner.set_style(
        ProgressStyle::default_spinner()
            .template("{spinner} {msg}")
            .expect("snapshot spinner template should be valid"),
    );
    spinner.set_message(message.into());
    spinner.enable_steady_tick(Duration::from_millis(80));
    spinner
}

fn snapshot_status_request(
    client: &reqwest::blocking::Client,
    url: &str,
) -> Result<serde_json::Value, String> {
    let request_json = serde_json::json!({
        "method": "snapshot_status",
        "params": [{}]
    });
    let response = client
        .post(url)
        .header("Content-Type", "application/json")
        .body(request_json.to_string())
        .send()
        .map_err(|error| format!("snapshot status request failed: {error}"))?;
    let text = response
        .text()
        .map_err(|error| format!("snapshot status response failed: {error}"))?;
    let json: serde_json::Value = serde_json::from_str(&text)
        .map_err(|error| format!("invalid snapshot status response: {error}"))?;
    let result = json["result"].clone();
    if result["status"].as_str() == Some("error") {
        let message = result["error_message"]
            .as_str()
            .or_else(|| result["error"].as_str())
            .unwrap_or("unknown snapshot status error");
        return Err(message.to_owned());
    }
    Ok(result)
}

fn run_export_snapshot(url: &str, output: &str) -> bool {
    let spinner = snapshot_spinner(format!("Requesting snapshot export to {output}..."));
    let request_json = serde_json::json!({
        "method": "export_snapshot",
        "params": [{"output": output}]
    });
    let client = reqwest::blocking::Client::builder()
        .timeout(Duration::from_secs(30))
        .build()
        .expect("snapshot RPC client should build");

    let response = match client
        .post(url)
        .header("Content-Type", "application/json")
        .body(request_json.to_string())
        .send()
    {
        Ok(response) => response,
        Err(error) => {
            spinner.finish_and_clear();
            eprintln!("Failed to connect to node at {url}: {error}");
            eprintln!("Make sure the node is running and the RPC port is accessible.");
            return false;
        }
    };

    let text = response.text().unwrap_or_default();
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else {
        spinner.finish_and_clear();
        eprintln!("{text}");
        return false;
    };
    let result = &json["result"];
    if result["status"].as_str() != Some("started") {
        spinner.finish_and_clear();
        if let Some(error) = result["error_message"].as_str() {
            eprintln!("  ✗ {error}");
        } else {
            eprintln!("{text}");
        }
        return false;
    }

    let ledger_seq = result["ledger_seq"].as_u64().unwrap_or_default();
    spinner.set_message(format!("Exporting snapshot (ledger seq: {ledger_seq})..."));
    let mut poll_failures = 0_u8;
    loop {
        thread::sleep(Duration::from_secs(1));
        match snapshot_status_request(&client, url) {
            Ok(status) => {
                poll_failures = 0;
                match status["state"].as_str().unwrap_or("unavailable") {
                    "running" => {
                        let sequence = status["ledger_seq"].as_u64().unwrap_or(ledger_seq);
                        spinner
                            .set_message(format!("Exporting snapshot (ledger seq: {sequence})..."));
                    }
                    "completed" => {
                        spinner.finish_with_message("✓ Snapshot export complete");
                        println!(
                            "  → Output: {}",
                            status["output"].as_str().unwrap_or(output)
                        );
                        if let Some(bytes) = status["file_size"].as_u64() {
                            println!("  → Size: {bytes} bytes");
                        }
                        return true;
                    }
                    "failed" => {
                        spinner.finish_and_clear();
                        eprintln!(
                            "  ✗ Snapshot export failed: {}",
                            status["error"].as_str().unwrap_or("unknown error")
                        );
                        return false;
                    }
                    "idle" => {
                        spinner.finish_and_clear();
                        eprintln!("  ✗ Snapshot export status was reset before completion.");
                        return false;
                    }
                    _ => {
                        spinner.finish_and_clear();
                        println!("  ✓ Export started (ledger seq: {ledger_seq})");
                        println!("  → Output: {output}");
                        println!(
                            "  → This node does not expose export progress; monitor its snapshot logs."
                        );
                        return true;
                    }
                }
            }
            Err(error) => {
                poll_failures = poll_failures.saturating_add(1);
                if error.contains("Unknown command") || error.contains("unknownCmd") {
                    spinner.finish_and_clear();
                    println!("  ✓ Export started (ledger seq: {ledger_seq})");
                    println!("  → Output: {output}");
                    println!(
                        "  → This node does not expose export progress; monitor its snapshot logs."
                    );
                    return true;
                }
                if poll_failures < 3 {
                    spinner.set_message("Waiting to reconnect for snapshot status...".to_owned());
                    continue;
                }
                spinner.finish_and_clear();
                println!("  ✓ Export started (ledger seq: {ledger_seq})");
                println!("  → Output: {output}");
                println!(
                    "  → Lost progress polling ({error}); the background export may still be running."
                );
                return true;
            }
        }
    }
}

fn run_load_snapshot(input: &str, conf: Option<&str>) -> bool {
    use nodestore::{DummyScheduler, Manager, ManagerImp, NullJournal, snapshot::load_snapshot};
    use std::path::Path;

    let config = match load_config_for_snapshot(conf) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error loading config: {e}");
            return false;
        }
    };

    let node_db = match config.section("node_db") {
        s if s.exists("path") => s.clone(),
        _ => {
            eprintln!("Error: [node_db] section with 'path' not found in config");
            return false;
        }
    };

    // Resolve sharded NuDB layout: actual files live in xrpldb.NNNN subdirectories.
    let mut node_db = node_db;
    if let Ok(Some(base_path)) = node_db.get::<String>("path") {
        let writable_path = Path::new(&base_path).join("xrpldb.0000");
        if writable_path.join("nudb.dat").exists() {
            node_db.set("path", writable_path.to_string_lossy().into_owned());
        }
    }

    let manager = ManagerImp::instance();
    let scheduler: Arc<dyn nodestore::Scheduler> = Arc::new(DummyScheduler);
    let journal: Arc<dyn nodestore::NodeStoreJournal> = Arc::new(NullJournal);

    let backend = match manager.make_backend(&node_db, 0, scheduler, journal) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("Error creating backend: {e}");
            return false;
        }
    };

    if let Err(e) = backend.open(true) {
        eprintln!("Error opening backend: {e}");
        return false;
    }

    let input_path = Path::new(input);
    let spinner = snapshot_spinner(format!(
        "Importing snapshot from {}...",
        input_path.display()
    ));

    match load_snapshot(backend.as_ref(), input_path) {
        Ok(manifest) => {
            backend.sync();
            let _ = backend.close();
            spinner.finish_with_message("✓ Snapshot import complete and integrity verified");
            println!(
                "  → Ledger seq: {}, chunks: {}",
                manifest.ledger_seq,
                manifest.chunks.len()
            );
            true
        }
        Err(e) => {
            spinner.finish_and_clear();
            eprintln!("Snapshot load failed: {e}");
            let _ = backend.close();
            false
        }
    }
}

fn load_config_for_snapshot(conf: Option<&str>) -> Result<BasicConfig, String> {
    let default_path = "/etc/quaxar/quaxar.cfg";
    let config_path = conf.unwrap_or(default_path);
    load_basic_config_file(Path::new(config_path))
}
