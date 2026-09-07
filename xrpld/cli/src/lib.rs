use clap::{Parser, Subcommand};

pub mod account;
pub mod amendments;
pub mod benchmark;
pub mod config_check;
pub mod db_stats;
pub mod doctor;
pub mod fee;
pub mod health;
pub mod interactive;
pub mod ledger_audit;
pub mod ledger_cmd;
pub mod log_level;
pub mod logo;
pub mod peers;
pub mod rpc_cmd;
pub mod status;
pub mod stop;
pub mod sync_status;
pub mod validator_keys;
pub mod validators;
pub mod version;

#[derive(Parser)]
#[command(name = "quaxar", about = "Quaxar XRPL Node", version)]
pub struct Cli {
    /// Subcommand to run. Startup flags without a subcommand start the node;
    /// a completely bare invocation prints help and exits.
    #[command(subcommand)]
    pub command: Option<Command>,

    /// RPC endpoint URL
    #[arg(long, default_value = "http://127.0.0.1:5005", global = true)]
    pub rpc_url: String,

    /// Config file path (for config check and node startup)
    #[arg(long, short, global = true)]
    pub conf: Option<String>,
}

#[derive(Subcommand)]
pub enum Command {
    /// Show node status (state, peers, validated ledger, uptime)
    Status,
    /// Reachability check — exits 0 when server_info succeeds, 1 if it fails
    Health,
    /// List connected peers with details
    Peers,
    /// Show sync progress (useful during initial sync)
    SyncStatus,
    /// Raw RPC call: quaxar rpc <method> ['{"json":"params"}']
    Rpc {
        /// RPC method name, for example server_info or can_delete
        method: String,
        /// JSON params object, or JSON array for multi-param JSON-RPC calls
        params: Option<String>,
        /// Print compact JSON instead of pretty JSON
        #[arg(long)]
        raw: bool,
    },
    /// Ping the local RPC server
    Ping,
    /// Show raw server_info RPC output
    ServerInfo,
    /// Show raw server_state RPC output
    ServerState,
    /// Show raw server_definitions RPC output
    ServerDefinitions,
    /// Show the latest closed ledger
    LedgerClosed,
    /// Show the current open ledger index
    LedgerCurrent,
    /// Show the validated ledger header
    LedgerHeader,
    /// Show fetch/acquisition state
    FetchInfo,
    /// Show raw get_counts output
    GetCounts,
    /// Get or set can_delete for advisory online delete
    CanDelete {
        /// Ledger sequence/hash or now/always/never
        value: Option<String>,
    },
    /// Rotate logs
    LogRotate,
    /// Generate random bytes via RPC
    Random,
    /// Show validator_info
    ValidatorInfo,
    /// Show validator_list_sites
    ValidatorListSites,
    /// Show UNL list
    UnlList,
    /// Show consensus_info
    ConsensusInfo,
    /// Show tx_reduce_relay state
    TxReduceRelay,
    /// Show database statistics (NuDB size, entries, hit rate)
    DbStats,
    /// Get or set the log level at runtime
    LogLevel {
        /// New log level to set (trace, debug, info, warn, error)
        level: Option<String>,
    },
    /// Validate config file without starting the node
    #[command(name = "config")]
    ConfigCheck,
    /// Pre-flight check: config, ports, disk, connectivity
    Doctor,
    /// Show version, git commit, build info
    Version,
    /// List trusted validators
    Validators,
    /// Show enabled/supported amendments
    Amendments,
    /// Show current fee info
    Fee,
    /// Show ledger details
    Ledger {
        /// Ledger sequence (omit for validated)
        seq: Option<u64>,
    },
    /// Download an immutable canonical-ledger audit fixture for offline replay
    #[command(name = "ledger-audit")]
    LedgerAudit {
        /// Canonical network to query
        #[arg(long, value_parser = ["testnet", "mainnet"])]
        network: String,
        /// Ledger sequence or 64-character ledger hash
        #[arg(long)]
        ledger: String,
        /// Directory to create for the immutable capture
        #[arg(long)]
        output: std::path::PathBuf,
        /// Override the canonical JSON-RPC endpoint
        #[arg(long)]
        source_url: Option<String>,
    },
    /// Show account info
    Account {
        /// Account address (rXXX...)
        address: String,
    },
    /// Graceful node shutdown
    Stop,
    /// Connect to a peer
    Connect {
        /// Peer address (ip:port)
        address: String,
    },
    /// Run crypto/serialization benchmarks
    Benchmark,
    /// Validator key management
    #[command(name = "validator-keys")]
    ValidatorKeys {
        #[command(subcommand)]
        action: ValidatorKeysAction,
    },
    /// Interactive CLI mode
    #[command(name = "cli")]
    Cli,
    /// Export a snapshot of the node store to a file
    #[command(name = "export-snapshot")]
    ExportSnapshot {
        /// Output file path for the snapshot
        #[arg(long, short)]
        output: String,
    },
    /// Load a snapshot file into the node store
    #[command(name = "load-snapshot")]
    LoadSnapshot {
        /// Input snapshot file path
        #[arg(long, short)]
        input: String,
    },
}

#[derive(Subcommand)]
pub enum ValidatorKeysAction {
    /// Generate a new validator keypair
    Generate,
    /// Create a validator token (manifest)
    CreateToken {
        /// Master secret hex (reads from validator-keys.json if omitted)
        #[arg(long)]
        secret: Option<String>,
    },
    /// Sign data with the validator master key
    Sign {
        /// Data to sign
        data: String,
    },
    /// Create a revocation manifest
    Revoke,
    /// Show validator public key and creation date
    Show,
}

// ─── UI Helpers (Kiro-style output formatting) ───────────────────────────────

/// Format a number with comma separators (e.g. 104452398 → "104,452,398")
pub fn format_number(n: u64) -> String {
    let s = n.to_string();
    let mut result = String::with_capacity(s.len() + s.len() / 3);
    for (i, c) in s.chars().rev().enumerate() {
        if i > 0 && i % 3 == 0 {
            result.push(',');
        }
        result.push(c);
    }
    result.chars().rev().collect()
}

/// Print a spaced-dash section separator (dimmed)
pub fn section_separator() {
    let dim = console::Style::new().dim();
    println!(
        "    {}",
        dim.apply_to("─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─")
    );
}

/// Print a key-value pair with 4-space indent, label dim and right-padded to 18 chars
pub fn kv(label: &str, value: &str) {
    let dim = console::Style::new().dim();
    let bold = console::Style::new().bold();
    println!(
        "    {} {}",
        dim.apply_to(format!("{:<18}", label)),
        bold.apply_to(value)
    );
}

/// Print a bold section header with 4-space indent
pub fn section_header(title: &str) {
    println!("    {}", console::Style::new().bold().apply_to(title));
}

/// Print an error line with red dot
pub fn print_error(msg: &str) {
    eprintln!("    {} {}", console::Style::new().red().apply_to("●"), msg);
}

/// Send an RPC request and return the parsed JSON result.
pub fn rpc_call(
    url: &str,
    method: &str,
    params: serde_json::Value,
) -> Result<serde_json::Value, String> {
    rpc_call_params(url, method, vec![params])
}

/// Send an RPC request with an explicit JSON-RPC params array and return the parsed result.
pub fn rpc_call_params(
    url: &str,
    method: &str,
    params: Vec<serde_json::Value>,
) -> Result<serde_json::Value, String> {
    let body = serde_json::json!({
        "method": method,
        "params": params
    });
    let resp = ureq::post(url)
        .set("Content-Type", "application/json")
        .send_string(&body.to_string())
        .map_err(|e| format!("Connection failed: {url}: {e}"))?;
    let text = resp
        .into_string()
        .map_err(|e| format!("Read failed: {e}"))?;
    let json: serde_json::Value =
        serde_json::from_str(&text).map_err(|e| format!("Invalid JSON: {e}"))?;
    let result = &json["result"];
    if result["status"].as_str() == Some("error") {
        let msg = result["error_message"]
            .as_str()
            .or_else(|| result["error"].as_str())
            .unwrap_or("Unknown error");
        return Err(msg.to_owned());
    }
    Ok(result.clone())
}

/// RPC call with a spinner shown while waiting.
#[cfg(test)]
#[path = "tests.rs"]
mod tests;
