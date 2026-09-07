//! Immutable canonical-ledger capture for the offline differential replay harness.
//!
//! This command deliberately captures data only. It never opens a configured
//! Quaxar NodeStore and it never attempts to use the running validator's data.
//! A later replay stage consumes this fixture through a read-only NodeStore.

use indicatif::{ProgressBar, ProgressStyle};
use serde_json::{Value, json};
use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::path::Path;

use crate::{format_number, kv, print_error};

use super::import::import_parent;

const TESTNET_RPC: &str = "https://s.altnet.rippletest.net:51234/";
// Ripple documents s2 as its full-history Mainnet public cluster.
const MAINNET_RPC: &str = "https://s2.ripple.com:51234/";
const PAGE_SIZE: u32 = 2_048;

fn endpoint(network: &str, override_url: Option<&str>) -> Option<String> {
    override_url.map(str::to_owned).or_else(|| match network {
        "testnet" => Some(TESTNET_RPC.to_owned()),
        "mainnet" => Some(MAINNET_RPC.to_owned()),
        _ => None,
    })
}

fn selector(ledger: &str) -> Value {
    ledger
        .parse::<u32>()
        .map(Value::from)
        .unwrap_or_else(|_| json!(ledger))
}

fn rpc(
    client: &reqwest::blocking::Client,
    url: &str,
    method: &str,
    params: Value,
) -> Result<Value, String> {
    let response = client
        .post(url)
        .json(&json!({"method": method, "params": [params]}))
        .send()
        .map_err(|error| format!("{method} request failed: {error}"))?;
    let status = response.status();
    let body: Value = response
        .json()
        .map_err(|error| format!("{method} returned invalid JSON: {error}"))?;
    if !status.is_success() {
        return Err(format!("{method} returned HTTP {status}: {body}"));
    }
    let result = body
        .get("result")
        .cloned()
        .ok_or_else(|| format!("{method} response omitted result: {body}"))?;
    if let Some(error) = result.get("error") {
        return Err(format!("{method} failed: {error}"));
    }
    Ok(result)
}

fn write_json(path: &Path, value: &Value) -> Result<(), String> {
    let file = File::create(path).map_err(|error| format!("create {}: {error}", path.display()))?;
    serde_json::to_writer_pretty(BufWriter::new(file), value)
        .map_err(|error| format!("write {}: {error}", path.display()))
}

/// Stream every `ledger_data` page to a JSONL file. The RPC server's marker is
/// opaque, so it is retained verbatim until the server explicitly omits it.
/// This is deliberately not a `Vec<Value>`: a full production ledger must not
/// make the CLI's resident set proportional to the state size.
fn stream_state(
    client: &reqwest::blocking::Client,
    url: &str,
    ledger_hash: &str,
    path: &Path,
    spinner: &ProgressBar,
    label: &str,
) -> Result<u64, String> {
    let file = File::create(path).map_err(|error| format!("create {}: {error}", path.display()))?;
    let mut state = BufWriter::new(file);
    let mut marker: Option<Value> = None;
    let mut entries = 0_u64;
    loop {
        spinner.set_message(format!("Downloading {label} state: {entries} entries"));
        let mut params = json!({"ledger_hash": ledger_hash, "binary": true, "limit": PAGE_SIZE});
        if let Some(marker) = marker.as_ref()
            && let Some(object) = params.as_object_mut()
        {
            object.insert("marker".to_owned(), marker.clone());
        }
        let page = rpc(client, url, "ledger_data", params)?;
        let rows = page["state"]
            .as_array()
            .ok_or_else(|| "ledger_data response omitted binary state entries".to_owned())?;
        for row in rows {
            serde_json::to_writer(&mut state, row)
                .map_err(|error| format!("write {}: {error}", path.display()))?;
            state
                .write_all(b"\n")
                .map_err(|error| format!("write {}: {error}", path.display()))?;
            entries += 1;
        }
        marker = page.get("marker").cloned();
        if marker.is_none() {
            break;
        }
    }
    state
        .flush()
        .map_err(|error| format!("flush {}: {error}", path.display()))?;
    Ok(entries)
}

/// Capture a canonical child ledger and its complete binary state page-by-page.
///
/// The output is intentionally append-only while downloading: state entries are
/// streamed to `state.jsonl`, so capture memory stays bounded regardless of the
/// ledger size. The fixture is not a NodeStore itself; converting it to one is
/// deliberately a separate verified import step.
pub fn run(network: &str, ledger: &str, output: &Path, source_url: Option<&str>) -> bool {
    let Some(url) = endpoint(network, source_url) else {
        print_error("network must be testnet or mainnet");
        return false;
    };
    if output.exists() {
        print_error(&format!(
            "refusing to overwrite existing fixture {}",
            output.display()
        ));
        return false;
    }
    if let Err(error) = fs::create_dir_all(output) {
        print_error(&format!("create {}: {error}", output.display()));
        return false;
    }

    let spinner = ProgressBar::new_spinner();
    spinner.set_style(
        ProgressStyle::default_spinner()
            .template("{spinner} {msg}")
            .expect("valid progress template"),
    );
    spinner.enable_steady_tick(std::time::Duration::from_millis(80));
    spinner.set_message(format!("Fetching canonical {network} ledger {ledger}..."));

    let client = match reqwest::blocking::Client::builder()
        .timeout(std::time::Duration::from_secs(60))
        .build()
    {
        Ok(client) => client,
        Err(error) => {
            spinner.finish_and_clear();
            print_error(&format!("build HTTP client: {error}"));
            return false;
        }
    };
    let ledger_result = match rpc(
        &client,
        &url,
        "ledger",
        json!({"ledger_index": selector(ledger), "transactions": true, "expand": true, "binary": true}),
    ) {
        Ok(result) => result,
        Err(error) => {
            spinner.finish_and_clear();
            print_error(&error);
            let _ = fs::remove_dir(output);
            return false;
        }
    };
    let canonical_index = ledger_result["ledger_index"].as_u64().or_else(|| {
        ledger_result["ledger_index"]
            .as_str()
            .and_then(|value| value.parse().ok())
    });
    let Some(canonical_index) = canonical_index else {
        spinner.finish_and_clear();
        print_error("canonical ledger response omitted a numeric ledger_index");
        return false;
    };
    if let Err(error) = write_json(&output.join("child-ledger.json"), &ledger_result) {
        spinner.finish_and_clear();
        print_error(&error);
        return false;
    }

    let parent_hash = ledger_result["ledger"]["parent_hash"].as_str();
    let Some(parent_hash) = parent_hash else {
        spinner.finish_and_clear();
        print_error("canonical child ledger omitted parent_hash");
        return false;
    };
    let parent_result = match rpc(
        &client,
        &url,
        "ledger",
        json!({"ledger_hash": parent_hash, "transactions": false, "expand": false, "binary": true}),
    ) {
        Ok(result) => result,
        Err(error) => {
            spinner.finish_and_clear();
            print_error(&format!("fetch canonical parent: {error}"));
            return false;
        }
    };
    let parent_index = parent_result["ledger_index"].as_u64().or_else(|| {
        parent_result["ledger_index"]
            .as_str()
            .and_then(|value| value.parse().ok())
    });
    let Some(parent_index) = parent_index else {
        spinner.finish_and_clear();
        print_error("canonical parent response omitted a numeric ledger_index");
        return false;
    };
    if parent_result["ledger_hash"].as_str() != Some(parent_hash)
        || parent_index.saturating_add(1) != canonical_index
    {
        spinner.finish_and_clear();
        print_error("canonical parent response is not the requested direct parent");
        return false;
    }
    let Some(child_hash) = ledger_result["ledger_hash"].as_str() else {
        spinner.finish_and_clear();
        print_error("canonical child response omitted ledger_hash");
        return false;
    };
    if let Err(error) = write_json(&output.join("parent-ledger.json"), &parent_result) {
        spinner.finish_and_clear();
        print_error(&error);
        return false;
    }
    let parent_entries = match stream_state(
        &client,
        &url,
        parent_hash,
        &output.join("parent-state.jsonl"),
        &spinner,
        "canonical parent",
    ) {
        Ok(entries) => entries,
        Err(error) => {
            spinner.finish_and_clear();
            print_error(&error);
            return false;
        }
    };
    let child_entries = match stream_state(
        &client,
        &url,
        child_hash,
        &output.join("child-state.jsonl"),
        &spinner,
        "canonical child",
    ) {
        Ok(entries) => entries,
        Err(error) => {
            spinner.finish_and_clear();
            print_error(&error);
            return false;
        }
    };
    spinner.set_message("Rebuilding and verifying disk-backed parent SHAMap...");
    let (rebuilt_parent_root, imported_parent_entries) = match import_parent(output) {
        Ok(import) => import,
        Err(error) => {
            spinner.finish_and_clear();
            print_error(&format!("disk-backed SHAMap import failed: {error}"));
            return false;
        }
    };
    let expected_parent_root = parent_result["ledger"]["account_hash"]
        .as_str()
        .or_else(|| parent_result["account_hash"].as_str());
    if expected_parent_root != Some(rebuilt_parent_root.as_str())
        || imported_parent_entries != parent_entries
    {
        spinner.finish_and_clear();
        print_error(&format!(
            "parent SHAMap verification failed: expected root {}, rebuilt root {}, expected {} leaves, imported {}",
            expected_parent_root.unwrap_or("<missing>"),
            rebuilt_parent_root,
            parent_entries,
            imported_parent_entries
        ));
        return false;
    }
    let transactions = ledger_result["ledger"]["transactions"]
        .as_array()
        .map_or(0, Vec::len);
    let manifest = json!({
        "format": "quaxar-ledger-audit-capture-v1",
        "network": network,
        "source_url": url,
        "ledger_index": canonical_index,
        "ledger_hash": ledger_result["ledger_hash"],
        "parent_hash": ledger_result["ledger"]["parent_hash"],
        "account_hash": ledger_result["ledger"]["account_hash"],
        "transaction_hash": ledger_result["ledger"]["transaction_hash"],
        "parent": {"ledger_index": parent_index, "ledger_hash": parent_result["ledger_hash"], "state_entries": parent_entries, "rebuilt_account_hash": rebuilt_parent_root},
        "child": {"ledger_index": canonical_index, "ledger_hash": ledger_result["ledger_hash"], "state_entries": child_entries},
        "transactions": transactions,
        "files": {
            "parent_ledger": "parent-ledger.json",
            "parent_state": "parent-state.jsonl",
            "child_ledger": "child-ledger.json",
            "child_state": "child-state.jsonl"
        }
    });
    if let Err(error) = write_json(&output.join("manifest.json"), &manifest) {
        spinner.finish_and_clear();
        print_error(&error);
        return false;
    }
    spinner.finish_and_clear();
    println!(
        "  {} Canonical ledger captured",
        console::Style::new().green().apply_to("●")
    );
    kv("Network", network);
    kv("Parent ledger", &parent_index.to_string());
    kv("Child ledger", &canonical_index.to_string());
    kv("Parent state", &format_number(parent_entries));
    kv("Child state", &format_number(child_entries));
    kv("Parent root", &rebuilt_parent_root);
    kv("Transactions", &format_number(transactions as u64));
    kv("Fixture", &output.display().to_string());
    println!("\n  Capture is immutable and does not use the running node's NuDB.");
    println!("  The fixture contains both complete snapshots and the child transaction set.");
    true
}
