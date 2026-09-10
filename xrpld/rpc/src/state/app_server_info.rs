//! Narrow app-backed `server_info` / `server_state` source above the landed
//! `ApplicationRoot` owner shell.

use std::collections::BTreeMap;
use std::sync::Arc;

use overlay::Overlay;

use basics::{
    base_uint::{Uint160, Uint256},
    chrono::NetClockTimePoint,
    hardened_hash::HardenedHashBuilder,
    sha_map_hash::SHAMapHash,
    tagged_cache::MonotonicClock,
};
use nodestore::{FetchType, NodeObjectType as NodeStoreObjectType};
use protocol::{
    AccountID, JsonOptions, JsonValue, Keylet, LedgerEntryType, NodePublicKey, STLedgerEntry,
    Serializer, StBase, TxSearched, account_keylet, feature_clawback, feature_token_escrow,
    owner_dir_keylet, page_keylet, signers_keylet, unchecked_keylet,
};
use shamap::family::{
    NullFullBelowCache, NullMissingNodeReporter, SHAMapFamily, SHAMapNodeFetcher,
};
use shamap::node_object::NodeObject as SHAMapNodeObject;
use shamap::storage::NodeObjectType as SHAMapNodeObjectType;
use shamap::traversal::TraversalError;
use shamap::tree_node_cache::TreeNodeCache;
use time::Duration;

use crate::handlers::FeeSource;
use crate::handlers::LedgerClosed;
use crate::handlers::LedgerClosedSource;
use crate::handlers::LedgerCurrentSource;
use crate::handlers::TransactionEntrySource;
use crate::handlers::TxHistorySource;
use crate::handlers::TxSource;
use crate::handlers::account_info::{AccountInfoSource, AccountQueueTransaction};
use crate::handlers::account_lines::AccountLinesSource;
use crate::handlers::account_tx::{
    AccountTxLedgerRange, AccountTxMarker, AccountTxPage, AccountTxQuery, AccountTxSource,
};
use crate::handlers::ledger_entry::LedgerEntrySource;
use crate::handlers::manifest::ManifestSource;
use crate::handlers::{LedgerLookupLedger, LedgerLookupSource};
use crate::state::RpcRuntime;
use crate::state::ServerInfoSource;
use crate::state::app_server_info_counters::append_counters_fields;
use crate::state::app_server_info_fee::append_load_factor_fields;
use crate::state::app_server_info_ledger::append_ledger_fields;
use crate::state::app_server_info_load::append_load_fields;
use crate::state::app_server_info_meta::append_runtime_metadata;
use crate::state::app_server_info_ports::append_ports_field;
use crate::state::app_server_info_source::AppServerInfoView;
use crate::state::app_server_info_state_accounting::append_state_accounting_fields;
use crate::state::app_server_info_status::append_status_snapshot_fields;
use crate::state::app_server_info_time::append_time_field;
use crate::state::app_server_info_validator::append_validator_fields;
use crate::state::app_server_info_warnings::build_server_info_warnings;
use crate::state::{TxHistoryRow, TxLookupError, TxLookupOutcome, TxRecord};
use crate::status::Status;
use app::paths::PathFindTuning;
use app::paths::PathFinderRequest;
use app::paths::PathFinderSource;
use app::{ApplicationRoot, JobType, NetworkOpsOperatingMode};
use ledger::LedgerMasterCaughtUp;

#[derive(Clone)]
pub struct ApplicationServerInfo<V> {
    view: V,
}

type RpcStateFamily = SHAMapFamily<
    MonotonicClock,
    HardenedHashBuilder,
    NullFullBelowCache,
    RpcStateNodeStoreFetcher,
    NullMissingNodeReporter,
>;

impl<V> ApplicationServerInfo<V> {
    pub const fn new(view: V) -> Self {
        Self { view }
    }
}

fn fee_json_from_report(report: tx::QueueTxQRpcReport) -> JsonValue {
    let mut result = BTreeMap::from([
        (
            "current_ledger_size".to_owned(),
            JsonValue::String(report.current_ledger_size),
        ),
        (
            "current_queue_size".to_owned(),
            JsonValue::String(report.current_queue_size),
        ),
        (
            "drops".to_owned(),
            JsonValue::Object(BTreeMap::from([
                (
                    "base_fee".to_owned(),
                    JsonValue::String(report.drops.base_fee),
                ),
                (
                    "median_fee".to_owned(),
                    JsonValue::String(report.drops.median_fee),
                ),
                (
                    "minimum_fee".to_owned(),
                    JsonValue::String(report.drops.minimum_fee),
                ),
                (
                    "open_ledger_fee".to_owned(),
                    JsonValue::String(report.drops.open_ledger_fee),
                ),
            ])),
        ),
        (
            "expected_ledger_size".to_owned(),
            JsonValue::String(report.expected_ledger_size),
        ),
        (
            "ledger_current_index".to_owned(),
            JsonValue::Unsigned(u64::from(report.ledger_current_index)),
        ),
        (
            "levels".to_owned(),
            JsonValue::Object(BTreeMap::from([
                (
                    "median_level".to_owned(),
                    JsonValue::String(report.levels.median_level),
                ),
                (
                    "minimum_level".to_owned(),
                    JsonValue::String(report.levels.minimum_level),
                ),
                (
                    "open_ledger_level".to_owned(),
                    JsonValue::String(report.levels.open_ledger_level),
                ),
                (
                    "reference_level".to_owned(),
                    JsonValue::String(report.levels.reference_level),
                ),
            ])),
        ),
    ]);

    if let Some(size) = report.max_queue_size {
        result.insert("max_queue_size".to_owned(), JsonValue::String(size));
    }

    JsonValue::Object(result)
}

impl<V: AppServerInfoView> ServerInfoSource for ApplicationServerInfo<V> {
    fn get_server_info(&self, human: bool, admin: bool, counters: bool) -> JsonValue {
        let mut info = BTreeMap::new();
        let mut status_snapshot = self.view.status_snapshot();

        // Derive complete_ledgers from the validated/closed ledger when the
        // status-rpc-state hasn't been populated yet (e.g. standalone or early
        // startup).
        if status_snapshot.complete_ledgers.is_none() {
            if let Some(ledger) = self
                .view
                .validated_ledger()
                .or_else(|| self.view.closed_ledger())
            {
                let seq = ledger.header().seq;
                if seq > 0 {
                    status_snapshot.complete_ledgers = Some(format!("{}-{}", seq, seq));
                } else {
                    status_snapshot.complete_ledgers = Some("empty".to_owned());
                }
            }
        }

        append_runtime_metadata(&mut info, &status_snapshot, human, admin);
        append_time_field(&mut info, &self.view);
        append_validator_fields(&mut info, &self.view, human, admin);

        let warnings = build_server_info_warnings(&self.view, admin);
        if !warnings.is_empty() {
            info.insert("warnings".to_owned(), JsonValue::Array(warnings));
        }

        info.insert(
            "server_state".to_owned(),
            JsonValue::String(
                self.view
                    .network_ops_operating_mode_string(admin)
                    .to_owned(),
            ),
        );

        if self.view.need_network_ledger() {
            info.insert(
                "network_ledger".to_owned(),
                JsonValue::String("waiting".to_owned()),
            );
        }

        if self.view.amendment_blocked() {
            info.insert("amendment_blocked".to_owned(), JsonValue::Bool(true));
        }

        append_status_snapshot_fields(&mut info, &self.view, &status_snapshot, human);
        append_ledger_fields(&mut info, &self.view, human);
        append_load_fields(&mut info, &self.view, admin);
        append_counters_fields(&mut info, &self.view, counters);
        append_state_accounting_fields(&mut info, &self.view);
        append_load_factor_fields(&mut info, &status_snapshot, &self.view, human, admin);
        append_ports_field(&mut info, &self.view, admin);

        if let Some((public_key, _)) = self.view.node_identity() {
            info.insert(
                "pubkey_node".to_owned(),
                JsonValue::String(public_key.to_node_public_base58()),
            );
        }

        JsonValue::Object(info)
    }
}

impl<V: AppServerInfoView> FeeSource for ApplicationServerInfo<V> {
    fn fee_json(&self) -> JsonValue {
        self.view
            .status_snapshot()
            .queue_report
            .map(fee_json_from_report)
            .unwrap_or(JsonValue::Null)
    }

    fn network_synced(&self) -> bool {
        RpcRuntime::network_synced(self)
    }
}

impl<V: AppServerInfoView> LedgerCurrentSource for ApplicationServerInfo<V> {
    fn current_ledger_index(&self) -> u32 {
        self.view
            .status_snapshot()
            .current_ledger_index
            .unwrap_or_default()
    }
}

impl<V: AppServerInfoView> LedgerClosedSource for ApplicationServerInfo<V> {
    fn closed_ledger(&self) -> Option<LedgerClosed> {
        self.view.closed_ledger().map(|ledger| LedgerClosed {
            seq: ledger.header().seq,
            hash: *ledger.header().hash.as_uint256(),
        })
    }
}

impl<V: AppServerInfoView> RpcRuntime for ApplicationServerInfo<V> {
    fn app(&self) -> Option<&ApplicationRoot> {
        self.view.app()
    }

    fn current_ledger_for_simulation(&self) -> Option<std::sync::Arc<ledger::Ledger>> {
        self.view
            .closed_ledger()
            .or_else(|| self.view.validated_ledger())
    }

    fn peers_get(&self) -> JsonValue {
        self.view
            .app()
            .and_then(|app| app.overlay_runtime())
            .map(|o| {
                let peers = o.overlay().peers_json();
                protocol::json!({ "peers": peers })
            })
            .unwrap_or_else(|| protocol::json!({ "peers": [] }))
    }

    fn network_ops_runtime(&self) -> Option<std::sync::Arc<app::AppNetworkOpsRuntime>> {
        self.view.network_ops_runtime()
    }

    fn job_queue(&self) -> Option<app::JobQueue> {
        Some(self.view.job_queue())
    }

    fn client_job_count(&self) -> u32 {
        u32::try_from(self.view.job_queue().job_count_ge(JobType::JtClient)).unwrap_or(u32::MAX)
    }

    fn has_current_ledger(&self) -> bool {
        self.view.status_snapshot().current_ledger_index.is_some()
            || self.view.validated_ledger().is_some()
            || self.view.closed_ledger().is_some()
    }

    fn has_closed_ledger(&self) -> bool {
        self.view.closed_ledger().is_some()
    }

    fn network_synced(&self) -> bool {
        if self.view.need_network_ledger() {
            return false;
        }

        if self.view.standalone() {
            return true;
        }

        // Syncing, Tracking, and Full all satisfy the condition. Use the
        // underlying operating mode, not the admin-only presentation overlay.
        self.view.network_ops_operating_mode() >= NetworkOpsOperatingMode::Syncing
    }

    fn validated_ledger_age(&self) -> std::time::Duration {
        self.view.validated_ledger_age()
    }

    fn path_search_max(&self) -> u32 {
        self.view.path_search_max()
    }

    fn path_search_old(&self) -> u32 {
        self.view.path_search_old()
    }

    fn path_search(&self) -> u32 {
        self.view.path_search()
    }

    fn path_search_fast(&self) -> u32 {
        self.view.path_search_fast()
    }

    fn current_ledger_index(&self) -> Option<u32> {
        self.view.status_snapshot().current_ledger_index
    }

    fn standalone(&self) -> bool {
        self.view.standalone()
    }

    fn ledger_accept(&self) -> Status {
        if !self.view.standalone() {
            return Status::new(crate::status::RpcErrorCode::NotStandalone);
        }

        self.view
            .accept_standalone_ledger()
            .map(|_| Status::OK)
            .unwrap_or_else(|_| Status::new(crate::status::RpcErrorCode::Internal))
    }

    fn ledger_request(&self, seq: u32) -> Status {
        self.app().map_or_else(
            || Status::new(crate::status::RpcErrorCode::NotImplemented),
            |app| <ApplicationRoot as RpcRuntime>::ledger_request(app, seq),
        )
    }

    fn ledger_request_by_hash(&self, hash: Uint256) -> Status {
        self.app().map_or_else(
            || Status::new(crate::status::RpcErrorCode::NotImplemented),
            |app| <ApplicationRoot as RpcRuntime>::ledger_request_by_hash(app, hash),
        )
    }

    fn export_snapshot(&self, output_path: &str) -> Result<protocol::JsonValue, String> {
        self.app().map_or_else(
            || Err("Application not available".to_owned()),
            |app| <ApplicationRoot as RpcRuntime>::export_snapshot(app, output_path),
        )
    }

    fn snapshot_status(&self) -> protocol::JsonValue {
        self.app().map_or_else(
            || protocol::json!({ "status": "success", "state": "unavailable" }),
            <ApplicationRoot as RpcRuntime>::snapshot_status,
        )
    }

    fn log_level_set(&self, partition: String, level: String) -> crate::status::Status {
        self.app().map_or_else(
            || crate::status::Status::new(crate::status::RpcErrorCode::NotImplemented),
            |app| <ApplicationRoot as RpcRuntime>::log_level_set(app, partition, level),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::{ApplicationServerInfo, RpcRuntime};
    use app::{ApplicationRoot, ApplicationRootOptions};
    use ledger::Ledger;
    use rpc::state::app_server_info_source::OwnedApplicationServerInfo;
    use rpc::status::RpcErrorCode;
    use std::sync::Arc;

    #[test]
    fn owned_application_server_info_ledger_request_uses_live_runtime_path() {
        let app = ApplicationRoot::with_options(ApplicationRootOptions::default())
            .expect("app should build");
        let source =
            ApplicationServerInfo::new(OwnedApplicationServerInfo::from_application_root(&app));

        let status = source.ledger_request(1);
        assert_eq!(status.error_code(), Some(RpcErrorCode::NoNetwork));

        let hash_status = source.ledger_request_by_hash(basics::base_uint::Uint256::zero());
        assert_eq!(hash_status.error_code(), Some(RpcErrorCode::NoNetwork));
    }

    #[test]
    fn owned_application_server_info_network_synced_mode_gate_without_caught_up_ledgers() {
        let app = ApplicationRoot::with_options(ApplicationRootOptions::default())
            .expect("app should build");

        let close_time = app.current_close_time_seconds();
        let ledger = std::sync::Arc::new(ledger::Ledger::from_ledger_seq_and_close_time(
            512,
            close_time.saturating_sub(1),
            false,
        ));
        app.on_validated_ledger(ledger);

        app.set_network_ops_operating_mode(app::NetworkOpsOperatingMode::Full);
        app.set_need_network_ledger(false);
        let source =
            ApplicationServerInfo::new(OwnedApplicationServerInfo::from_application_root(&app));

        assert!(source.network_synced());
    }

    #[test]
    fn owned_application_server_info_network_synced_rejects_need_network_ledger_even_in_full() {
        let app = ApplicationRoot::with_options(ApplicationRootOptions::default())
            .expect("app should build");
        let close_time = app.current_close_time_seconds();
        let ledger = Arc::new(Ledger::from_ledger_seq_and_close_time(
            512,
            close_time.saturating_sub(1),
            false,
        ));

        app.on_published_ledger(Arc::clone(&ledger));
        let _ = app.on_validated_ledger(Arc::clone(&ledger));
        app.set_network_ops_operating_mode(app::NetworkOpsOperatingMode::Full);
        app.set_need_network_ledger(true);

        let source =
            ApplicationServerInfo::new(OwnedApplicationServerInfo::from_application_root(&app));
        assert!(!source.network_synced());
    }

    #[test]
    fn owned_application_server_info_network_synced_accepts_tracking_when_caught_up() {
        let app = ApplicationRoot::with_options(ApplicationRootOptions::default())
            .expect("app should build");
        let close_time = app.current_close_time_seconds();
        let ledger = Arc::new(Ledger::from_ledger_seq_and_close_time(
            1024,
            close_time.saturating_sub(1),
            false,
        ));

        app.on_published_ledger(Arc::clone(&ledger));
        let _ = app.on_validated_ledger(Arc::clone(&ledger));
        app.set_need_network_ledger(false);
        app.set_network_ops_operating_mode(app::NetworkOpsOperatingMode::Tracking);

        let source =
            ApplicationServerInfo::new(OwnedApplicationServerInfo::from_application_root(&app));
        assert!(source.network_synced());
    }

    #[test]
    fn amm_info_current_ledger_uses_parent_ledger_close_time() {
        use rpc::amm::amm_info::AmmInfoSource;
        use rpc::ledger_lookup::LedgerLookupSource;

        let app = ApplicationRoot::with_options(ApplicationRootOptions::default())
            .expect("app should build");
        let parent_close_time = 840_000_123;
        let ledger = Arc::new(Ledger::from_ledger_seq_and_close_time(
            2048,
            parent_close_time + 100,
            false,
        ));
        let _ = app.on_validated_ledger(ledger);
        let _ = app.open_ledger().modify(|open| {
            open.ledger_current_index = 2049;
            open.parent_close_time = parent_close_time;
            open.close_time_resolution = 10;
            true
        });
        let source =
            ApplicationServerInfo::new(OwnedApplicationServerInfo::from_application_root(&app));
        let current = source
            .get_current_ledger()
            .expect("current ledger lookup should use the validated parent");

        assert!(current.open);
        assert_eq!(source.parent_close_time(&current), parent_close_time);
    }
}

impl<V: AppServerInfoView> PathFinderSource for ApplicationServerInfo<V> {
    fn path_find_tuning(&self) -> PathFindTuning {
        PathFindTuning {
            old: self.view.path_search_old(),
            search: self.view.path_search(),
            fast: self.view.path_search_fast(),
            max: self.view.path_search_max(),
        }
    }

    fn find_paths(
        &self,
        request: &PathFinderRequest,
        params: &JsonValue,
        _search_level: u32,
        _is_legacy: bool,
        api_version: u32,
        previous_paths: &BTreeMap<protocol::Asset, protocol::STPathSet>,
    ) -> Result<app::paths::PathFinderResult, crate::RpcStatus> {
        let explicit_ledger = matches!(params, JsonValue::Object(object)
            if object.contains_key("ledger")
                || object.contains_key("ledger_hash")
                || object.contains_key("ledger_index"));
        let (ledger, validated) = if explicit_ledger {
            let context = crate::handlers::LedgerLookupContext {
                params,
                source: self,
                api_version,
                role: crate::handlers::RpcRole::User,
            };
            let (selected, _) = crate::handlers::lookup_ledger_with_result(&context)?;
            (
                resolve_lookup_ledger(&self.view, &selected),
                Some(self.is_validated(&selected)),
            )
        } else {
            (self.view.closed_ledger(), None)
        };
        let ledger =
            ledger.ok_or_else(|| crate::RpcStatus::new(crate::RpcErrorCode::LedgerNotFound))?;
        let app = self
            .view
            .app()
            .ok_or_else(|| crate::RpcStatus::new(crate::RpcErrorCode::Internal))?;
        let mut result = super::ripple_path_find_engine::find_paths(
            app,
            ledger,
            request,
            _search_level,
            _is_legacy,
            previous_paths,
        )?;
        result.validated = validated;
        Ok(result)
    }
}

fn ledger_lookup_ledger(ledger: &ledger::Ledger, open: bool) -> LedgerLookupLedger {
    LedgerLookupLedger {
        hash: *ledger.header().hash.as_uint256(),
        seq: ledger.header().seq,
        open,
    }
}

fn find_ledger_by_seq<V: AppServerInfoView>(view: &V, seq: u32) -> Option<LedgerLookupLedger> {
    view.validated_ledger()
        .filter(|ledger| ledger.header().seq == seq)
        .map(|ledger| ledger_lookup_ledger(ledger.as_ref(), false))
        .or_else(|| {
            view.closed_ledger()
                .filter(|ledger| ledger.header().seq == seq)
                .map(|ledger| ledger_lookup_ledger(ledger.as_ref(), false))
        })
        .or_else(|| {
            view.published_ledger()
                .filter(|ledger| ledger.header().seq == seq)
                .map(|ledger| ledger_lookup_ledger(ledger.as_ref(), false))
        })
}

fn best_non_open_ledger<V: AppServerInfoView>(view: &V) -> Option<std::sync::Arc<ledger::Ledger>> {
    let validated = view.validated_ledger();
    let closed = view.closed_ledger();
    let published = view.published_ledger();

    [validated, closed, published]
        .into_iter()
        .flatten()
        .max_by_key(|ledger| ledger.header().seq)
}

fn find_ledger_hash_by_seq<V: AppServerInfoView>(view: &V, seq: u32) -> Option<Uint256> {
    find_ledger_by_seq(view, seq).map(|ledger| ledger.hash)
}

fn find_close_time_by_seq<V: AppServerInfoView>(view: &V, seq: u32) -> Option<NetClockTimePoint> {
    view.validated_ledger()
        .filter(|ledger| ledger.header().seq == seq)
        .map(|ledger| NetClockTimePoint::new(ledger.header().close_time))
        .or_else(|| {
            view.closed_ledger()
                .filter(|ledger| ledger.header().seq == seq)
                .map(|ledger| NetClockTimePoint::new(ledger.header().close_time))
        })
        .or_else(|| {
            view.published_ledger()
                .filter(|ledger| ledger.header().seq == seq)
                .map(|ledger| NetClockTimePoint::new(ledger.header().close_time))
        })
}

fn resolve_lookup_ledger<V: AppServerInfoView>(
    view: &V,
    ledger: &LedgerLookupLedger,
) -> Option<std::sync::Arc<ledger::Ledger>> {
    if ledger.open {
        return view
            .closed_ledger()
            .or_else(|| view.published_ledger())
            .or_else(|| view.validated_ledger());
    }

    view.validated_ledger()
        .filter(|candidate| {
            candidate.header().seq == ledger.seq
                && *candidate.header().hash.as_uint256() == ledger.hash
        })
        .or_else(|| {
            view.closed_ledger().filter(|candidate| {
                candidate.header().seq == ledger.seq
                    && *candidate.header().hash.as_uint256() == ledger.hash
            })
        })
        .or_else(|| {
            view.published_ledger().filter(|candidate| {
                candidate.header().seq == ledger.seq
                    && *candidate.header().hash.as_uint256() == ledger.hash
            })
        })
        .or_else(|| get_ledger_obj(view, ledger.seq, ledger.hash))
}

#[derive(Clone)]
struct RpcStateNodeStoreFetcher {
    node_store: app::SHAMapStoreNodeStore,
}

impl RpcStateNodeStoreFetcher {
    fn new(node_store: app::SHAMapStoreNodeStore) -> Self {
        Self { node_store }
    }
}

impl SHAMapNodeFetcher for RpcStateNodeStoreFetcher {
    fn fetch_node_object(&self, hash: SHAMapHash, ledger_seq: u32) -> Option<SHAMapNodeObject> {
        let fetched = match &self.node_store {
            app::SHAMapStoreNodeStore::Single(database) => database.fetch_node_object(
                hash.as_uint256(),
                ledger_seq,
                FetchType::Synchronous,
                false,
            ),
            app::SHAMapStoreNodeStore::Rotating(database) => database.fetch_node_object(
                hash.as_uint256(),
                ledger_seq,
                FetchType::Synchronous,
                false,
            ),
        }?;

        Some(SHAMapNodeObject::new(
            match fetched.object_type() {
                NodeStoreObjectType::Ledger => SHAMapNodeObjectType::Ledger,
                NodeStoreObjectType::AccountNode => SHAMapNodeObjectType::AccountNode,
                NodeStoreObjectType::TransactionNode => SHAMapNodeObjectType::TransactionNode,
                NodeStoreObjectType::Unknown | NodeStoreObjectType::Dummy => {
                    SHAMapNodeObjectType::Unknown
                }
            },
            fetched.data().to_vec(),
            *fetched.hash(),
        ))
    }
}

fn build_rpc_state_family(app: &ApplicationRoot) -> Option<RpcStateFamily> {
    let node_store = app.node_store().as_ref()?.clone();
    Some(SHAMapFamily::new(
        Arc::new(TreeNodeCache::new(
            "rpc-server-info-read",
            2048,
            Duration::seconds(30),
            MonotonicClock::default(),
        )),
        NullFullBelowCache::new(1),
        RpcStateNodeStoreFetcher::new(node_store),
        NullMissingNodeReporter,
    ))
}

fn with_lookup_ledger_family<T, F>(
    app: &ApplicationRoot,
    resolved: &ledger::Ledger,
    work: F,
) -> Option<T>
where
    F: FnOnce(&ledger::Ledger, &RpcStateFamily) -> Option<T>,
{
    let family = build_rpc_state_family(app)?;
    let (hydrated, _loaded) = ledger::Ledger::load_immutable_with_family(
        resolved.header().clone(),
        false,
        &ledger::NullLedgerJournal,
        &family,
    );

    work(&hydrated, &family)
}

fn read_lookup_ledger_entry_with_family(
    app: &ApplicationRoot,
    resolved: &ledger::Ledger,
    keylet: Keylet,
) -> Option<STLedgerEntry> {
    with_lookup_ledger_family(app, resolved, |hydrated, family| {
        hydrated.read_with_family(keylet, family).ok().flatten()
    })
}

fn succ_lookup_ledger_key_with_family(
    app: &ApplicationRoot,
    resolved: &ledger::Ledger,
    key: Uint256,
    last: Option<Uint256>,
) -> Option<Uint256> {
    with_lookup_ledger_family(app, resolved, |hydrated, family| {
        hydrated.succ_with_family(key, last, family).ok().flatten()
    })
}

fn read_lookup_ledger_entry<V: AppServerInfoView>(
    view: &V,
    ledger: &LedgerLookupLedger,
    keylet: Keylet,
) -> Option<STLedgerEntry> {
    // `ledger_index: current` is the mutable OpenLedger state, not its last
    // closed parent.  The persistent submit sandbox is Quaxar's OpenView;
    // using the parent here made every current-ledger RPC lag one close and
    // hid newly created or deleted objects from account_objects, account_info,
    // and the other sources routed through this helper.
    if ledger.open
        && let Some(current) = view
            .app()
            .and_then(|app| app.current_open_ledger_entry(keylet))
    {
        return current.ok().flatten();
    }

    let resolved = resolve_lookup_ledger(view, ledger)?;
    match resolved.read(keylet) {
        Ok(Some(entry)) => Some(entry),
        Ok(None) | Err(_) => view
            .app()
            .and_then(|app| read_lookup_ledger_entry_with_family(app, resolved.as_ref(), keylet)),
    }
}

fn succ_lookup_ledger_key<V: AppServerInfoView>(
    view: &V,
    ledger: &LedgerLookupLedger,
    key: Uint256,
    last: Option<Uint256>,
) -> Option<Uint256> {
    if ledger.open
        && let Some(current) = view
            .app()
            .and_then(|app| app.current_open_ledger_successor(key, last))
    {
        return current.ok().flatten();
    }

    let resolved = resolve_lookup_ledger(view, ledger)?;
    match resolved.succ(key, last) {
        Ok(Some(entry)) => Some(entry),
        Ok(None) | Err(_) => view
            .app()
            .and_then(|app| succ_lookup_ledger_key_with_family(app, resolved.as_ref(), key, last)),
    }
}

fn lookup_sql_transaction_by_hash<V: AppServerInfoView>(
    view: &V,
    hash: Uint256,
) -> Option<(u32, String, Vec<u8>, Vec<u8>, Option<u32>)> {
    let transaction_db = view
        .app()
        .and_then(|app| app.relational_database().as_ref().cloned())
        .and_then(|relational| relational.transaction_db())?;
    let connection = transaction_db.get_session();

    let hash_text = hash.to_string();
    let row = connection
        .query_row(
            "SELECT LedgerSeq, Status, RawTxn, TxnMeta FROM Transactions WHERE TransID = ?1 LIMIT 1",
            (hash_text.as_str(),),
            |row| {
                Ok((
                    row.get::<_, u32>(0)?,
                    row.get::<_, String>(1)?,
                    row.get::<_, Vec<u8>>(2)?,
                    row.get::<_, Vec<u8>>(3)?,
                ))
            },
        )
        .ok()?;

    let txn_seq = connection
        .query_row(
            "SELECT TxnSeq FROM AccountTransactions WHERE TransID = ?1 AND LedgerSeq = ?2 ORDER BY TxnSeq ASC LIMIT 1",
            (hash_text.as_str(), i64::from(row.0)),
            |row| row.get::<_, u32>(0),
        )
        .ok();

    Some((row.0, row.1, row.2, row.3, txn_seq))
}

fn lookup_sql_tx_record<V: AppServerInfoView>(
    view: &V,
    hash: Uint256,
) -> Result<Option<TxRecord>, TxLookupError> {
    let Some((ledger_seq, status, raw_txn, raw_meta, txn_seq)) =
        lookup_sql_transaction_by_hash(view, hash)
    else {
        return Ok(None);
    };

    let mut converted = Vec::new();
    app::convert_blobs_to_tx_result(
        &mut converted,
        ledger_seq,
        &status,
        &raw_txn,
        &raw_meta,
        view.network_id(),
    )
    .map_err(|_| TxLookupError::DatabaseDeserialization)?;

    Ok(converted.into_iter().next().map(|entry| TxRecord {
        txn: std::sync::Arc::clone(entry.transaction.get_s_transaction()),
        meta: Some(entry.meta),
        ledger_index: ledger_seq,
        close_time: find_close_time_by_seq(view, ledger_seq),
        ledger_hash: find_ledger_hash_by_seq(view, ledger_seq),
        validated: true,
        txn_index: txn_seq,
        network_id: Some(view.network_id()),
    }))
}

/// Return the current validated transaction directly from its `TransactionMd`
/// SHAMap leaf. SQL is the durable transaction-history index, but ledger
/// validation becomes RPC-visible before its relational save can be observed
/// by a concurrent `tx` request. Falling through to TransactionMaster in that
/// window loses the metadata and therefore `meta.TransactionResult`.
fn lookup_validated_ledger_tx_record<V: AppServerInfoView>(
    view: &V,
    hash: Uint256,
) -> Option<TxRecord> {
    let ledger = view.validated_ledger()?;
    let (txn, meta) = ledger.tx_read(hash).ok().flatten()?;
    let ledger_index = ledger.header().seq;

    Some(TxRecord {
        txn,
        txn_index: Some(meta.get_index()),
        meta: Some(meta),
        ledger_index,
        close_time: Some(NetClockTimePoint::new(ledger.header().close_time)),
        ledger_hash: Some(*ledger.header().hash.as_uint256()),
        validated: true,
        network_id: Some(view.network_id()),
    })
}

impl<V: AppServerInfoView> LedgerLookupSource for ApplicationServerInfo<V> {
    fn get_ledger_by_hash(&self, hash: Uint256) -> Option<LedgerLookupLedger> {
        self.view
            .validated_ledger()
            .filter(|ledger| *ledger.header().hash.as_uint256() == hash)
            .map(|ledger| ledger_lookup_ledger(ledger.as_ref(), false))
            .or_else(|| {
                self.view
                    .closed_ledger()
                    .filter(|ledger| *ledger.header().hash.as_uint256() == hash)
                    .map(|ledger| ledger_lookup_ledger(ledger.as_ref(), false))
            })
            .or_else(|| {
                self.view
                    .published_ledger()
                    .filter(|ledger| *ledger.header().hash.as_uint256() == hash)
                    .map(|ledger| ledger_lookup_ledger(ledger.as_ref(), false))
            })
            .or_else(|| {
                get_ledger_obj(&self.view, 0, hash)
                    .map(|ledger| ledger_lookup_ledger(ledger.as_ref(), false))
            })
    }

    fn get_ledger_by_seq(&self, seq: u32) -> Option<LedgerLookupLedger> {
        find_ledger_by_seq(&self.view, seq).or_else(|| {
            get_ledger_obj(&self.view, seq, Uint256::zero())
                .map(|ledger| ledger_lookup_ledger(ledger.as_ref(), false))
        })
    }

    fn get_current_ledger(&self) -> Option<LedgerLookupLedger> {
        let snapshot_seq = self.view.status_snapshot().current_ledger_index;
        let fallback_seq = self
            .view
            .closed_ledger()
            .map(|ledger| ledger.header().seq.saturating_add(1))
            .or_else(|| {
                self.view
                    .validated_ledger()
                    .map(|ledger| ledger.header().seq.saturating_add(1))
            });
        let seq = match (snapshot_seq, fallback_seq) {
            (Some(snapshot), Some(fallback)) if snapshot < fallback => fallback,
            (Some(snapshot), _) => snapshot,
            (None, Some(fallback)) => fallback,
            (None, None) => return None,
        };

        Some(LedgerLookupLedger {
            hash: Uint256::zero(),
            seq,
            open: true,
        })
    }

    fn get_closed_ledger(&self) -> Option<LedgerLookupLedger> {
        self.view
            .closed_ledger()
            .map(|ledger| ledger_lookup_ledger(ledger.as_ref(), false))
    }

    fn get_validated_ledger(&self) -> Option<LedgerLookupLedger> {
        best_non_open_ledger(&self.view).map(|ledger| ledger_lookup_ledger(ledger.as_ref(), false))
    }

    fn get_valid_ledger_index(&self) -> u32 {
        best_non_open_ledger(&self.view)
            .map(|ledger| ledger.header().seq)
            .unwrap_or_default()
    }

    fn get_validated_ledger_age(&self) -> std::time::Duration {
        self.view.validated_ledger_age()
    }

    fn is_validated(&self, ledger: &LedgerLookupLedger) -> bool {
        !ledger.open
            && best_non_open_ledger(&self.view).is_some_and(|candidate| {
                candidate.header().seq == ledger.seq
                    && *candidate.header().hash.as_uint256() == ledger.hash
            })
    }

    fn standalone(&self) -> bool {
        self.view.standalone()
    }
}

impl<V: AppServerInfoView> AccountInfoSource for ApplicationServerInfo<V> {
    fn read_account_root(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            account_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }

    fn read_signer_list(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            signers_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }

    fn feature_clawback_enabled(&self, ledger: &LedgerLookupLedger) -> bool {
        resolve_lookup_ledger(&self.view, ledger)
            .is_some_and(|resolved| resolved.rules().enabled(&feature_clawback()))
    }

    fn feature_token_escrow_enabled(&self, ledger: &LedgerLookupLedger) -> bool {
        resolve_lookup_ledger(&self.view, ledger)
            .is_some_and(|resolved| resolved.rules().enabled(&feature_token_escrow()))
    }

    fn account_queue_txs(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Vec<AccountQueueTransaction> {
        if !ledger.open {
            return Vec::new();
        }

        let Some(app) = self.view.app() else {
            return Vec::new();
        };

        if app.live_current_ledger_index() != Some(ledger.seq) {
            return Vec::new();
        }

        app.tx_q_account_txs(account_id)
            .into_iter()
            .map(Into::into)
            .collect()
    }
}

impl<V: AppServerInfoView> AccountLinesSource for ApplicationServerInfo<V> {
    fn read_account_root(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            account_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }

    fn read_owner_dir_page(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
        page_index: u64,
    ) -> Option<STLedgerEntry> {
        let root = owner_dir_keylet(Uint160::from_slice(account_id.data()).expect("account width"));
        let keylet = if page_index == 0 {
            root
        } else {
            page_keylet(root, page_index)
        };
        read_lookup_ledger_entry(&self.view, ledger, keylet)
    }

    fn read_child_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }
}

impl<V: AppServerInfoView> ManifestSource for ApplicationServerInfo<V> {
    fn get_master_key(&self, _requested: NodePublicKey) -> Option<NodePublicKey> {
        None
    }

    fn get_signing_key(&self, _master_key: NodePublicKey) -> Option<NodePublicKey> {
        None
    }

    fn get_manifest_blob(&self, _master_key: NodePublicKey) -> Option<Vec<u8>> {
        None
    }

    fn get_manifest_sequence(&self, _master_key: NodePublicKey) -> Option<u32> {
        None
    }

    fn get_manifest_domain(&self, _master_key: NodePublicKey) -> Option<String> {
        None
    }
}

impl<V: AppServerInfoView> LedgerEntrySource for ApplicationServerInfo<V> {
    fn read_ledger_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }
}

impl<V: AppServerInfoView> AccountTxSource for ApplicationServerInfo<V> {
    fn validated_range(&self) -> Option<AccountTxLedgerRange> {
        let max = self
            .view
            .validated_ledger()
            .map(|ledger| ledger.header().seq)
            .or_else(|| self.view.closed_ledger().map(|ledger| ledger.header().seq))?;

        Some(AccountTxLedgerRange { min: 1, max })
    }

    fn page(&self, query: &AccountTxQuery) -> Result<AccountTxPage, Status> {
        let mut page_rows: Vec<(crate::state::TxRecord, AccountTxMarker)> = Vec::new();

        let maybe_transaction_db = self
            .view
            .app()
            .and_then(|app| app.relational_database().as_ref().cloned())
            .and_then(|relational| relational.transaction_db());

        if let Some(transaction_db) = maybe_transaction_db {
            let connection = transaction_db.get_session();
            let sql = match (query.forward, query.marker) {
                (true, Some(_)) => {
                    "SELECT a.LedgerSeq, a.TxnSeq, t.Status, t.RawTxn, t.TxnMeta \
                     FROM AccountTransactions a \
                     JOIN Transactions t ON t.TransID = a.TransID \
                     WHERE a.Account = ?1 AND a.LedgerSeq BETWEEN ?2 AND ?3 \
                     AND (a.LedgerSeq > ?5 OR (a.LedgerSeq = ?5 AND a.TxnSeq > ?6)) \
                     ORDER BY a.LedgerSeq ASC, a.TxnSeq ASC \
                     LIMIT ?4"
                }
                (false, Some(_)) => {
                    "SELECT a.LedgerSeq, a.TxnSeq, t.Status, t.RawTxn, t.TxnMeta \
                     FROM AccountTransactions a \
                     JOIN Transactions t ON t.TransID = a.TransID \
                     WHERE a.Account = ?1 AND a.LedgerSeq BETWEEN ?2 AND ?3 \
                     AND (a.LedgerSeq < ?5 OR (a.LedgerSeq = ?5 AND a.TxnSeq < ?6)) \
                     ORDER BY a.LedgerSeq DESC, a.TxnSeq DESC \
                     LIMIT ?4"
                }
                (true, None) => {
                    "SELECT a.LedgerSeq, a.TxnSeq, t.Status, t.RawTxn, t.TxnMeta \
                     FROM AccountTransactions a \
                     JOIN Transactions t ON t.TransID = a.TransID \
                     WHERE a.Account = ?1 AND a.LedgerSeq BETWEEN ?2 AND ?3 \
                     ORDER BY a.LedgerSeq ASC, a.TxnSeq ASC \
                     LIMIT ?4"
                }
                (false, None) => {
                    "SELECT a.LedgerSeq, a.TxnSeq, t.Status, t.RawTxn, t.TxnMeta \
                     FROM AccountTransactions a \
                     JOIN Transactions t ON t.TransID = a.TransID \
                     WHERE a.Account = ?1 AND a.LedgerSeq BETWEEN ?2 AND ?3 \
                     ORDER BY a.LedgerSeq DESC, a.TxnSeq DESC \
                     LIMIT ?4"
                }
            };

            let fetch_limit = i64::from(query.limit.saturating_add(1));
            let mut statement = connection
                .prepare(sql)
                .map_err(|_| Status::new(crate::status::RpcErrorCode::Internal))?;

            let account = protocol::to_base58(query.account);
            match query.marker {
                Some(marker) => {
                    let rows = statement
                        .query_map(
                            (
                                account.as_str(),
                                i64::from(query.ledger_range.min),
                                i64::from(query.ledger_range.max),
                                fetch_limit,
                                i64::from(marker.ledger),
                                i64::from(marker.seq),
                            ),
                            |row| {
                                Ok((
                                    row.get::<_, u32>(0)?,
                                    row.get::<_, u32>(1)?,
                                    row.get::<_, String>(2)?,
                                    row.get::<_, Vec<u8>>(3)?,
                                    row.get::<_, Vec<u8>>(4)?,
                                ))
                            },
                        )
                        .map_err(|_| Status::new(crate::status::RpcErrorCode::Internal))?;

                    for row in rows {
                        let (ledger_seq, txn_seq, status, raw_txn, raw_meta) =
                            row.map_err(|_| Status::new(crate::status::RpcErrorCode::Internal))?;

                        let mut converted = Vec::new();
                        app::convert_blobs_to_tx_result(
                            &mut converted,
                            ledger_seq,
                            &status,
                            &raw_txn,
                            &raw_meta,
                            self.view.network_id(),
                        )
                        .map_err(|_| Status::new(crate::status::RpcErrorCode::DbDeserialization))?;

                        for entry in converted {
                            page_rows.push((
                                crate::state::TxRecord {
                                    txn: std::sync::Arc::clone(
                                        entry.transaction.get_s_transaction(),
                                    ),
                                    meta: Some(entry.meta),
                                    ledger_index: ledger_seq,
                                    close_time: find_close_time_by_seq(&self.view, ledger_seq),
                                    ledger_hash: find_ledger_hash_by_seq(&self.view, ledger_seq),
                                    validated: true,
                                    txn_index: Some(txn_seq),
                                    network_id: Some(self.view.network_id()),
                                },
                                AccountTxMarker {
                                    ledger: ledger_seq,
                                    seq: txn_seq,
                                },
                            ));
                        }
                    }
                }
                None => {
                    let rows = statement
                        .query_map(
                            (
                                account.as_str(),
                                i64::from(query.ledger_range.min),
                                i64::from(query.ledger_range.max),
                                fetch_limit,
                            ),
                            |row| {
                                Ok((
                                    row.get::<_, u32>(0)?,
                                    row.get::<_, u32>(1)?,
                                    row.get::<_, String>(2)?,
                                    row.get::<_, Vec<u8>>(3)?,
                                    row.get::<_, Vec<u8>>(4)?,
                                ))
                            },
                        )
                        .map_err(|_| Status::new(crate::status::RpcErrorCode::Internal))?;

                    for row in rows {
                        let (ledger_seq, txn_seq, status, raw_txn, raw_meta) =
                            row.map_err(|_| Status::new(crate::status::RpcErrorCode::Internal))?;

                        let mut converted = Vec::new();
                        app::convert_blobs_to_tx_result(
                            &mut converted,
                            ledger_seq,
                            &status,
                            &raw_txn,
                            &raw_meta,
                            self.view.network_id(),
                        )
                        .map_err(|_| Status::new(crate::status::RpcErrorCode::DbDeserialization))?;

                        for entry in converted {
                            page_rows.push((
                                crate::state::TxRecord {
                                    txn: std::sync::Arc::clone(
                                        entry.transaction.get_s_transaction(),
                                    ),
                                    meta: Some(entry.meta),
                                    ledger_index: ledger_seq,
                                    close_time: find_close_time_by_seq(&self.view, ledger_seq),
                                    ledger_hash: find_ledger_hash_by_seq(&self.view, ledger_seq),
                                    validated: true,
                                    txn_index: Some(txn_seq),
                                    network_id: Some(self.view.network_id()),
                                },
                                AccountTxMarker {
                                    ledger: ledger_seq,
                                    seq: txn_seq,
                                },
                            ));
                        }
                    }
                }
            }
        }

        let mut marker = None;
        if page_rows.len() > query.limit as usize {
            marker = page_rows
                .get(query.limit as usize - 1)
                .map(|(_, marker)| *marker);
            page_rows.truncate(query.limit as usize);
        }

        Ok(AccountTxPage {
            ledger_range: query.ledger_range,
            limit: query.limit,
            marker,
            transactions: page_rows.into_iter().map(|(record, _)| record).collect(),
        })
    }

    fn get_close_time_by_seq(&self, ledger_seq: u32) -> Option<NetClockTimePoint> {
        find_close_time_by_seq(&self.view, ledger_seq)
    }

    fn get_hash_by_seq(&self, ledger_seq: u32) -> Option<Uint256> {
        find_ledger_hash_by_seq(&self.view, ledger_seq)
    }
}

impl<V: AppServerInfoView> TxSource for ApplicationServerInfo<V> {
    fn tx_tables_enabled(&self) -> bool {
        true
    }

    fn network_id(&self) -> u32 {
        self.view.network_id()
    }

    fn network_synced(&self) -> bool {
        RpcRuntime::network_synced(self)
    }

    fn lookup_transaction_by_hash(
        &self,
        hash: Uint256,
        ledger_range: Option<(u32, u32)>,
    ) -> Result<TxLookupOutcome, TxLookupError> {
        let cached = if let Some(transaction) = self.view.fetch_cached_transaction(&hash) {
            let transaction = transaction
                .lock()
                .expect("transaction mutex must not be poisoned");

            Some(TxRecord {
                txn: std::sync::Arc::clone(transaction.get_s_transaction()),
                meta: None,
                ledger_index: transaction.get_ledger(),
                close_time: find_close_time_by_seq(&self.view, transaction.get_ledger()),
                ledger_hash: find_ledger_hash_by_seq(&self.view, transaction.get_ledger()),
                validated: transaction.is_validated(),
                txn_index: None,
                network_id: Some(self.view.network_id()),
            })
        } else {
            None
        };

        if let Some(record) = cached.as_ref()
            && !record.validated
        {
            return Ok(TxLookupOutcome::Found(record.clone()));
        }

        if let Some(record) = lookup_sql_tx_record(&self.view, hash)? {
            if let Some((min, max)) = ledger_range
                && (record.ledger_index < min || record.ledger_index > max)
            {
                return Ok(TxLookupOutcome::NotFound(TxSearched::Some));
            }

            return Ok(TxLookupOutcome::Found(record));
        }

        // The validated ledger is authoritative during the short interval
        // between validation visibility and SQL history persistence. Read its
        // TransactionMd leaf so `tx` retains the result metadata instead of
        // returning a cache-only record with no `meta.TransactionResult`.
        if let Some(record) = lookup_validated_ledger_tx_record(&self.view, hash) {
            if let Some((min, max)) = ledger_range
                && (record.ledger_index < min || record.ledger_index > max)
            {
                return Ok(TxLookupOutcome::NotFound(TxSearched::Some));
            }

            return Ok(TxLookupOutcome::Found(record));
        }

        // A TransactionMaster entry can be marked COMMITTED while its ledger
        // is still only a local consensus candidate. It has neither the
        // authoritative ledger validation proof nor TxMeta. Rippled therefore
        // reports it as unvalidated until the ledger lookup or transaction
        // history supplies both. Do not expose a metadata-less cache entry as
        // `validated: true`: callers use that flag to consume
        // `meta.TransactionResult` and would otherwise observe a false final
        // result during the persistence/validation handoff.
        if let Some(mut record) = cached {
            if let Some((min, max)) = ledger_range
                && (record.ledger_index < min || record.ledger_index > max)
            {
                return Ok(TxLookupOutcome::NotFound(TxSearched::Some));
            }

            record.validated = false;
            return Ok(TxLookupOutcome::Found(record));
        }

        Ok(TxLookupOutcome::NotFound(TxSearched::Unknown))
    }

    fn lookup_transaction_by_ctid(
        &self,
        ledger_seq: u32,
        txn_index: u16,
        ledger_range: Option<(u32, u32)>,
    ) -> Result<TxLookupOutcome, TxLookupError> {
        if let Some((min, max)) = ledger_range
            && (ledger_seq < min || ledger_seq > max)
        {
            return Ok(TxLookupOutcome::NotFound(TxSearched::Some));
        }
        if let Some(tx_hash) = self.view.txn_id_from_index(ledger_seq, txn_index as u32) {
            return self.lookup_transaction_by_hash(tx_hash, ledger_range);
        }
        Ok(TxLookupOutcome::NotFound(TxSearched::Unknown))
    }
}

impl<V: AppServerInfoView> TxHistorySource for ApplicationServerInfo<V> {
    type Row = TxHistoryRow;

    fn tx_tables_enabled(&self) -> bool {
        true
    }

    fn get_tx_history(&self, start_index: u32) -> Vec<Self::Row> {
        self.view
            .app()
            .and_then(|app| app.relational_database().as_ref().cloned())
            .map(|relational| {
                relational
                    .get_tx_history(start_index)
                    .into_iter()
                    .map(|transaction| TxHistoryRow { transaction })
                    .collect()
            })
            .unwrap_or_default()
    }
}

impl<V: AppServerInfoView> TransactionEntrySource for ApplicationServerInfo<V> {
    fn read_transaction_entry(
        &self,
        ledger: &LedgerLookupLedger,
        tx_hash: Uint256,
    ) -> Option<(protocol::STTx, Option<protocol::TxMeta>)> {
        if let Some(resolved) = resolve_lookup_ledger(&self.view, ledger)
            && let Ok(Some(entry)) = ledger::ReadView::tx_read(resolved.as_ref(), tx_hash)
        {
            let (tx, meta) = entry.into_parts();
            return Some((
                (*tx.as_ref()).clone(),
                meta.map(|meta| {
                    protocol::TxMeta::from_stobject(tx_hash, ledger.seq, (*meta).clone())
                }),
            ));
        }

        if let Some((ledger_seq, status, raw_txn, raw_meta, _txn_seq)) =
            lookup_sql_transaction_by_hash(&self.view, tx_hash)
            && ledger_seq == ledger.seq
        {
            let mut converted = Vec::new();
            app::convert_blobs_to_tx_result(
                &mut converted,
                ledger_seq,
                &status,
                &raw_txn,
                &raw_meta,
                self.view.network_id(),
            )
            .ok()?;

            if let Some(entry) = converted.into_iter().next() {
                return Some((
                    (*entry.transaction.get_s_transaction().as_ref()).clone(),
                    Some(entry.meta),
                ));
            }
        }

        let transaction = self.view.fetch_cached_transaction(&tx_hash)?;
        let transaction = transaction
            .lock()
            .expect("transaction mutex must not be poisoned");
        if transaction.is_validated() && transaction.get_ledger() == ledger.seq {
            return Some(((*transaction.get_s_transaction().as_ref()).clone(), None));
        }
        None
    }

    fn get_close_time_by_seq(&self, ledger_seq: u32) -> Option<NetClockTimePoint> {
        find_close_time_by_seq(&self.view, ledger_seq)
    }

    fn get_hash_by_seq(&self, ledger_seq: u32) -> Option<Uint256> {
        find_ledger_hash_by_seq(&self.view, ledger_seq)
    }
}

use crate::handlers::ledger::LedgerSource;
use crate::handlers::ledger_lookup::{RpcErrorCode, RpcStatus};
use app::{AppLedgerFill, get_json as app_get_json};
use ledger::LedgerFillOptions;

fn get_ledger_obj<V: AppServerInfoView>(
    view: &V,
    seq: u32,
    hash: Uint256,
) -> Option<std::sync::Arc<ledger::Ledger>> {
    if let Some(app) = view.app()
        && let Some(runtime) = app.ledger_master_runtime()
    {
        let ledger_master = runtime.ledger_master();
        if !hash.is_zero()
            && let Some(ledger) = ledger_master.get_ledger_by_hash(SHAMapHash::new(hash))
        {
            return Some(ledger);
        }
        if seq != 0
            && let Some(ledger) = ledger_master.get_ledger_by_seq(seq, &ledger::NullLedgerJournal)
        {
            return Some(ledger);
        }
    }

    if !hash.is_zero() {
        if let Some(l) = view
            .validated_ledger()
            .filter(|l| *l.header().hash.as_uint256() == hash)
        {
            return Some(l);
        }
        if let Some(l) = view
            .closed_ledger()
            .filter(|l| *l.header().hash.as_uint256() == hash)
        {
            return Some(l);
        }
        if let Some(l) = view
            .published_ledger()
            .filter(|l| *l.header().hash.as_uint256() == hash)
        {
            return Some(l);
        }
    }
    if seq != 0 {
        if let Some(l) = view.validated_ledger().filter(|l| l.header().seq == seq) {
            return Some(l);
        }
        if let Some(l) = view.closed_ledger().filter(|l| l.header().seq == seq) {
            return Some(l);
        }
        if let Some(l) = view.published_ledger().filter(|l| l.header().seq == seq) {
            return Some(l);
        }
    }
    None
}

impl<V: AppServerInfoView> LedgerSource for ApplicationServerInfo<V> {
    fn render_selected_ledger(
        &self,
        ledger_lookup: crate::handlers::ledger_lookup::LedgerLookupLedger,
        options: LedgerFillOptions,
    ) -> Result<JsonValue, RpcStatus> {
        if ledger_lookup.open {
            return self.render_open_ledger();
        }
        let ledger = get_ledger_obj(&self.view, ledger_lookup.seq, ledger_lookup.hash)
            .ok_or_else(|| RpcStatus::new(RpcErrorCode::LedgerNotFound))?;

        // For full/state/transaction dumps, use the family-aware path so
        // traversal can fetch released nodes from the NodeStore rather than
        // rendering an empty TransactionMd map.
        if options.contains(LedgerFillOptions::FULL)
            || options.contains(LedgerFillOptions::DUMP_STATE)
            || options.contains(LedgerFillOptions::DUMP_TXRP)
        {
            if let Some(app) = self.view.app()
                && let Some(family) = build_rpc_state_family(app)
            {
                let app_fill = app::AppLedgerFill::new(&ledger, options);
                return app::get_json_with_family(&app_fill, &family)
                    .map_err(|_| RpcStatus::new(RpcErrorCode::Internal));
            }
        }

        let fill = AppLedgerFill::new(&ledger, options);
        app_get_json(&fill).map_err(|_| RpcStatus::new(RpcErrorCode::Internal))
    }

    fn render_closed_ledger(&self) -> Result<JsonValue, RpcStatus> {
        let ledger = self
            .view
            .closed_ledger()
            .ok_or_else(|| RpcStatus::new(RpcErrorCode::LedgerNotFound))?;
        let options = LedgerFillOptions::FULL;
        let fill = AppLedgerFill::new(&ledger, options);
        app_get_json(&fill).map_err(|_| RpcStatus::new(RpcErrorCode::Internal))
    }

    fn render_open_ledger(&self) -> Result<JsonValue, RpcStatus> {
        let current = self
            .get_current_ledger()
            .ok_or_else(|| RpcStatus::new(RpcErrorCode::LedgerNotFound))?;
        let parent_hash = best_non_open_ledger(&self.view)
            .map(|ledger| ledger.header().hash.to_string())
            .unwrap_or_default();

        Ok(JsonValue::Object(BTreeMap::from([
            ("closed".to_owned(), JsonValue::Bool(false)),
            (
                "ledger_index".to_owned(),
                JsonValue::String(current.seq.to_string()),
            ),
            ("parent_hash".to_owned(), JsonValue::String(parent_hash)),
        ])))
    }
}

// --- Source trait implementations for newly wired handlers ---

impl<V: AppServerInfoView> crate::handlers::account_channels::AccountChannelsSource
    for ApplicationServerInfo<V>
{
    fn read_account_root(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            account_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }
    fn read_owner_dir_page(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
        page_index: u64,
    ) -> Option<STLedgerEntry> {
        let root = owner_dir_keylet(Uint160::from_slice(account_id.data()).expect("account width"));
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            if page_index == 0 {
                root
            } else {
                page_keylet(root, page_index)
            },
        )
    }
    fn read_ledger_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }
}

impl<V: AppServerInfoView> crate::handlers::account_currencies::AccountCurrenciesSource
    for ApplicationServerInfo<V>
{
    fn read_account_root(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            account_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }
    fn read_owner_dir_page(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
        page_index: u64,
    ) -> Option<STLedgerEntry> {
        let root = owner_dir_keylet(Uint160::from_slice(account_id.data()).expect("account width"));
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            if page_index == 0 {
                root
            } else {
                page_keylet(root, page_index)
            },
        )
    }
    fn read_child_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }
}

impl<V: AppServerInfoView> crate::handlers::account_offers::AccountOffersSource
    for ApplicationServerInfo<V>
{
    fn read_account_root(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            account_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }
    fn read_owner_dir_page(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
        page_index: u64,
    ) -> Option<STLedgerEntry> {
        let root = owner_dir_keylet(Uint160::from_slice(account_id.data()).expect("account width"));
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            if page_index == 0 {
                root
            } else {
                page_keylet(root, page_index)
            },
        )
    }
    fn read_child_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }
}

impl<V: AppServerInfoView> crate::handlers::deposit_authorized::DepositAuthorizedSource
    for ApplicationServerInfo<V>
{
    fn read_account_root(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            account_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }
    fn read_ledger_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }
    fn parent_close_time(&self, _ledger: &LedgerLookupLedger) -> u32 {
        self.view
            .closed_ledger()
            .map(|l| l.header().parent_close_time)
            .unwrap_or(0)
    }
}

impl<V: AppServerInfoView> crate::handlers::gateway_balances::GatewayBalancesSource
    for ApplicationServerInfo<V>
{
    fn read_account_root(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            account_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }
    fn read_owner_dir_page(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
        page_index: u64,
    ) -> Option<STLedgerEntry> {
        let root = owner_dir_keylet(Uint160::from_slice(account_id.data()).expect("account width"));
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            if page_index == 0 {
                root
            } else {
                page_keylet(root, page_index)
            },
        )
    }
    fn read_child_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }
}

impl<V: AppServerInfoView> crate::handlers::no_ripple_check::NoRippleCheckSource
    for ApplicationServerInfo<V>
{
    fn read_account_root(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            account_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }
    fn read_owner_dir_page(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
        page_index: u64,
    ) -> Option<STLedgerEntry> {
        let root = owner_dir_keylet(Uint160::from_slice(account_id.data()).expect("account width"));
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            if page_index == 0 {
                root
            } else {
                page_keylet(root, page_index)
            },
        )
    }
    fn read_child_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }
    fn transaction_fee_drops(&self, _ledger: &LedgerLookupLedger) -> u64 {
        self.view
            .closed_ledger()
            .map(|l| l.fees().base)
            .unwrap_or(10)
    }
}

impl<V: AppServerInfoView> crate::handlers::owner_info::OwnerInfoSource
    for ApplicationServerInfo<V>
{
    fn read_owner_dir_page(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
        page_index: u64,
    ) -> Option<STLedgerEntry> {
        let root = owner_dir_keylet(Uint160::from_slice(account_id.data()).expect("account width"));
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            if page_index == 0 {
                root
            } else {
                page_keylet(root, page_index)
            },
        )
    }
    fn read_child_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }
}

impl<V: AppServerInfoView> crate::handlers::validators::ValidatorsSource
    for ApplicationServerInfo<V>
{
    fn get_validators(&self) -> JsonValue {
        self.view.validators().get_json()
    }
}

impl<V: AppServerInfoView> crate::handlers::validator_list_sites::ValidatorListSitesSource
    for ApplicationServerInfo<V>
{
    fn get_validator_list_sites(&self) -> JsonValue {
        // ValidatorSite is not stored on the view — return empty for now.
        JsonValue::Object(BTreeMap::from([(
            "validator_sites".to_owned(),
            JsonValue::Array(Vec::new()),
        )]))
    }
}

impl<V: AppServerInfoView> crate::handlers::unl_list::UnlListSource for ApplicationServerInfo<V> {
    fn for_each_listed(&self, visitor: &mut dyn FnMut(protocol::NodePublicKey, bool)) {
        self.view.validators().for_each_listed(|pk, trusted| {
            visitor(pk.to_bytes(), trusted);
        });
    }
}

impl<V: AppServerInfoView> crate::handlers::consensus_info::ConsensusInfoSource
    for ApplicationServerInfo<V>
{
    fn get_consensus_info(&self) -> JsonValue {
        // Consensus state is not yet exposed on the view.
        JsonValue::Object(BTreeMap::new())
    }
}

impl<V: AppServerInfoView> crate::handlers::ledger_header::LedgerHeaderSource
    for ApplicationServerInfo<V>
{
    fn resolve_ledger_header(
        &self,
    ) -> Result<crate::handlers::ledger_header::LedgerHeaderResolved, crate::status::RpcStatus>
    {
        let ledger = self
            .view
            .validated_ledger()
            .or_else(|| self.view.closed_ledger())
            .ok_or_else(|| {
                crate::status::RpcStatus::new(crate::status::RpcErrorCode::LedgerNotFound)
            })?;
        let validated = self.view.validated_ledger().is_some();
        let mut base_json = BTreeMap::new();
        if validated {
            base_json.insert("validated".to_owned(), JsonValue::Bool(true));
        }
        Ok(crate::handlers::ledger_header::LedgerHeaderResolved {
            base_json: JsonValue::Object(base_json),
            header: ledger.header(),
        })
    }
}

impl<V: AppServerInfoView> crate::handlers::account_nfts::AccountNFTsSource
    for ApplicationServerInfo<V>
{
    fn read_account_root(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            account_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }
    fn read_nft_page(
        &self,
        ledger: &LedgerLookupLedger,
        page_key: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(page_key))
    }
    fn succ_nft_page(
        &self,
        ledger: &LedgerLookupLedger,
        key: Uint256,
        last: Uint256,
    ) -> Option<Uint256> {
        succ_lookup_ledger_key(&self.view, ledger, key, Some(last))
    }
}

impl<V: AppServerInfoView> crate::handlers::account_objects_support::AccountObjectsView
    for ApplicationServerInfo<V>
{
    fn read_entry(
        &self,
        keylet: Keylet,
    ) -> Result<Option<STLedgerEntry>, shamap::traversal::TraversalError> {
        let ledger = self
            .view
            .validated_ledger()
            .or_else(|| self.view.closed_ledger())
            .ok_or(shamap::traversal::TraversalError::MissingNode(
                basics::sha_map_hash::SHAMapHash::default(),
            ))?;
        let lookup = LedgerLookupLedger {
            hash: *ledger.header().hash.as_uint256(),
            seq: ledger.header().seq,
            open: false,
        };
        Ok(read_lookup_ledger_entry(&self.view, &lookup, keylet))
    }
    fn succ_key(
        &self,
        key: Uint256,
        last: Option<Uint256>,
    ) -> Result<Option<Uint256>, shamap::traversal::TraversalError> {
        let ledger = self
            .view
            .validated_ledger()
            .or_else(|| self.view.closed_ledger())
            .ok_or(shamap::traversal::TraversalError::MissingNode(
                basics::sha_map_hash::SHAMapHash::default(),
            ))?;
        let lookup = LedgerLookupLedger {
            hash: *ledger.header().hash.as_uint256(),
            seq: ledger.header().seq,
            open: false,
        };
        Ok(succ_lookup_ledger_key(&self.view, &lookup, key, last))
    }

    fn read_entry_at(
        &self,
        ledger: &LedgerLookupLedger,
        keylet: Keylet,
    ) -> Result<Option<STLedgerEntry>, shamap::traversal::TraversalError> {
        Ok(read_lookup_ledger_entry(&self.view, ledger, keylet))
    }

    fn succ_key_at(
        &self,
        ledger: &LedgerLookupLedger,
        key: Uint256,
        last: Option<Uint256>,
    ) -> Result<Option<Uint256>, shamap::traversal::TraversalError> {
        Ok(succ_lookup_ledger_key(&self.view, ledger, key, last))
    }
}

impl<V: AppServerInfoView> crate::handlers::book_changes::BookChangesSource
    for ApplicationServerInfo<V>
{
    fn book_changes_ledger(
        &self,
        ledger_lookup: LedgerLookupLedger,
    ) -> Option<crate::handlers::book_changes::BookChangesLedger> {
        let resolved = resolve_lookup_ledger(&self.view, &ledger_lookup)?;
        let ledger_time = resolved.header().close_time;

        // Walk the transaction map and extract (STTx, TxMeta) pairs.
        let mut transactions = Vec::new();
        if let Ok(txs) = ledger::ReadView::txs(resolved.as_ref()) {
            for read_view_tx in txs {
                let (tx_arc, meta_arc_opt) = read_view_tx.into_parts();
                let Some(meta_arc) = meta_arc_opt else {
                    continue;
                };
                let tx = (*tx_arc).clone();
                let meta = protocol::TxMeta::from_stobject(
                    Uint256::zero(),
                    resolved.header().seq,
                    (*meta_arc).clone(),
                );
                transactions
                    .push(crate::handlers::book_changes::BookChangesTransaction { txn: tx, meta });
            }
        }

        Some(crate::handlers::book_changes::BookChangesLedger {
            ledger_time,
            transactions,
        })
    }
}

impl<V: AppServerInfoView> crate::handlers::book_offers::BookOffersSource
    for ApplicationServerInfo<V>
{
    fn client_job_count_gt(&self, threshold: u32) -> bool {
        u32::try_from(self.view.job_queue().job_count_ge(JobType::JtClient)).unwrap_or(0)
            > threshold
    }
}

impl<V: AppServerInfoView> crate::handlers::get_counts::GetCountsSource
    for ApplicationServerInfo<V>
{
    fn use_tx_tables(&self) -> bool {
        false
    }
    fn db_kb_total(&self) -> u64 {
        0
    }
    fn db_kb_ledger(&self) -> u64 {
        0
    }
    fn db_kb_transaction(&self) -> u64 {
        0
    }
    fn local_tx_count(&self) -> usize {
        0
    }
    fn write_load(&self) -> JsonValue {
        JsonValue::Null
    }
    fn historical_perminute(&self) -> i64 {
        0
    }
    fn sle_hit_rate(&self) -> JsonValue {
        JsonValue::Null
    }
    fn ledger_hit_rate(&self) -> JsonValue {
        JsonValue::Null
    }
    fn accepted_ledger_cache_size(&self) -> u64 {
        self.view
            .app()
            .map(|app| app.accepted_ledger_cache().get_cache_size() as u64)
            .unwrap_or(0)
    }
    fn accepted_ledger_cache_hit_rate(&self) -> JsonValue {
        JsonValue::Null
    }
    fn fullbelow_size(&self) -> i64 {
        self.view
            .app()
            .map(|app| app.full_below_cache_size() as i64)
            .unwrap_or(0)
    }
    fn treenode_cache_size(&self) -> u64 {
        self.view
            .app()
            .and_then(|app| app.shared_tree_cache())
            .map(|cache| cache.get_cache_size() as u64)
            .unwrap_or(0)
    }
    fn treenode_cache_capacity_entries(&self) -> u64 {
        self.view
            .app()
            .and_then(|app| app.shared_tree_cache())
            .map(|cache| cache.total_capacity() as u64)
            .unwrap_or(0)
    }
    fn treenode_track_size(&self) -> u64 {
        self.view
            .app()
            .and_then(|app| app.shared_tree_cache())
            .map(|cache| cache.get_track_size() as u64)
            .unwrap_or(0)
    }
    fn add_node_store_counts(&self, json: &mut BTreeMap<String, JsonValue>) {
        let Some(app) = self.view.app() else {
            return;
        };
        let memory = shamap::tree_node::shamap_memory_stats();
        for (name, value) in [
            ("shamap_allocated_inner_nodes", memory.allocated_inner_nodes),
            ("shamap_allocated_leaf_nodes", memory.allocated_leaf_nodes),
            ("shamap_active_inner_nodes", memory.active_inner_nodes),
            ("shamap_active_leaf_nodes", memory.active_leaf_nodes),
            ("shamap_allocated_child_slots", memory.allocated_child_slots),
            ("shamap_loaded_child_links", memory.loaded_child_links),
            ("shamap_allocated_items", memory.allocated_items),
            ("shamap_allocated_item_bytes", memory.allocated_item_bytes),
            ("shamap_structural_bytes", memory.structural_bytes),
        ] {
            json.insert(name.to_owned(), JsonValue::Unsigned(value));
        }

        let profile =
            app::NodeSizeResourceProfile::for_node_size(app.status_rpc_node_size().as_deref());
        json.insert(
            "treenode_cache_target_size".to_owned(),
            JsonValue::Unsigned(profile.tree_cache_size as u64),
        );
        json.insert(
            "treenode_cache_target_age_seconds".to_owned(),
            JsonValue::Signed(profile.tree_cache_age_seconds),
        );
        json.insert(
            "ledger_cache_target_size".to_owned(),
            JsonValue::Unsigned(profile.ledger_history_cache_size as u64),
        );
        json.insert(
            "ledger_cache_target_age_seconds".to_owned(),
            JsonValue::Signed(profile.ledger_history_cache_age_seconds),
        );
        json.insert(
            "acquisition_max_sessions".to_owned(),
            JsonValue::Unsigned(profile.acquisition_max_sessions as u64),
        );

        let Some(node_store) = app.node_store().as_ref() else {
            return;
        };

        json.insert(
            "node_store".to_owned(),
            JsonValue::String(node_store.kind().to_owned()),
        );
        match node_store {
            app::SHAMapStoreNodeStore::Single(database) => {
                json.insert(
                    "node_db_earliest_seq".to_owned(),
                    JsonValue::Unsigned(u64::from(database.earliest_ledger_seq())),
                );
                database.add_counts_json(json);
            }
            app::SHAMapStoreNodeStore::Rotating(database) => {
                json.insert(
                    "node_db_earliest_seq".to_owned(),
                    JsonValue::Unsigned(u64::from(database.earliest_ledger_seq())),
                );
                database.add_counts_json(json);
            }
        }
    }
}

impl<V: AppServerInfoView> crate::handlers::print::PrintSource for ApplicationServerInfo<V> {
    fn print_json(&self, _path: Option<&str>) -> JsonValue {
        JsonValue::Object(BTreeMap::new())
    }
}

impl<V: AppServerInfoView> crate::handlers::validator_info::ValidatorInfoSource
    for ApplicationServerInfo<V>
{
    fn get_validation_public_key(&self) -> Option<protocol::NodePublicKey> {
        self.view.validation_public_key().map(|pk| pk.to_bytes())
    }
    fn get_master_key(
        &self,
        validation_public_key: protocol::NodePublicKey,
    ) -> protocol::NodePublicKey {
        let pk = protocol::PublicKey::from_bytes(validation_public_key);
        self.view.validators().master_key(pk).to_bytes()
    }
    fn get_manifest_blob(&self, _master_key: protocol::NodePublicKey) -> Option<Vec<u8>> {
        None
    }
    fn get_manifest_sequence(&self, _master_key: protocol::NodePublicKey) -> Option<u32> {
        None
    }
    fn get_manifest_domain(&self, _master_key: protocol::NodePublicKey) -> Option<String> {
        None
    }
}

impl<V: AppServerInfoView> crate::nft::nft_offers::NFTOffersSource for ApplicationServerInfo<V> {
    fn read_directory_page(
        &self,
        ledger: &LedgerLookupLedger,
        page_key: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(page_key))
    }
    fn read_nft_offer(
        &self,
        ledger: &LedgerLookupLedger,
        offer_key: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(offer_key))
    }
}

impl<V: AppServerInfoView> crate::handlers::book_offers::BookOffersRuntime
    for ApplicationServerInfo<V>
{
    fn get_book_page(
        &self,
        _ledger: &LedgerLookupLedger,
        book: protocol::Book,
        _taker: AccountID,
        _proof: bool,
        limit: u32,
        _marker: JsonValue,
        result: &mut JsonValue,
    ) {
        use protocol::{
            JsonOptions, Keylet, LedgerEntryType, get_book_base, get_field_by_symbol,
            get_quality_next,
        };

        let offers_array = JsonValue::Array(Vec::new());
        let JsonValue::Object(obj) = result else {
            *result = JsonValue::Object(std::collections::BTreeMap::from([(
                "offers".to_owned(),
                offers_array,
            )]));
            return;
        };

        let Some(ledger) = self
            .view
            .validated_ledger()
            .or_else(|| self.view.closed_ledger())
        else {
            obj.insert("offers".to_owned(), offers_array);
            return;
        };

        let book_base = get_book_base(book);
        let book_end = get_quality_next(book_base);
        let mut tip_index = book_base;
        let mut remaining = limit.min(256);
        let mut offers = Vec::new();
        let mut owner_balances = BTreeMap::<AccountID, protocol::STAmount>::new();
        let asset_is_global_frozen = |asset: protocol::Asset| match asset {
            protocol::Asset::Issue(issue) if issue.native() => false,
            protocol::Asset::Issue(issue) => Uint160::from_slice(issue.issuer().data())
                .and_then(|issuer| {
                    ledger::account_root_helpers::is_global_frozen(ledger.as_ref(), issuer).ok()
                })
                .unwrap_or(false),
            protocol::Asset::MPTIssue(issue) => {
                ledger::mptoken_helpers::is_global_frozen_mpt(ledger.as_ref(), &issue)
                    .unwrap_or(false)
            }
        };
        let global_freeze = asset_is_global_frozen(book.out) || asset_is_global_frozen(book.r#in);
        let transfer_rate = match book.out {
            protocol::Asset::Issue(issue) if issue.native() => protocol::PARITY_RATE,
            protocol::Asset::Issue(issue) => Uint160::from_slice(issue.issuer().data())
                .and_then(|issuer| {
                    ledger::account_root_helpers::transfer_rate(ledger.as_ref(), issuer).ok()
                })
                .map(protocol::Rate::new)
                .unwrap_or(protocol::PARITY_RATE),
            protocol::Asset::MPTIssue(issue) => {
                ledger::mptoken_helpers::transfer_rate_mpt(ledger.as_ref(), issue.mpt_id())
                    .unwrap_or(protocol::PARITY_RATE)
            }
        };

        while remaining > 0 {
            let next = match ledger.succ(tip_index, Some(book_end)) {
                Ok(Some(key)) => key,
                _ => break,
            };

            let dir_keylet = Keylet::new(LedgerEntryType::DirectoryNode, next);
            let dir_sle = match ledger.read(dir_keylet) {
                Ok(Some(sle)) => sle,
                _ => break,
            };

            let indexes = dir_sle.get_field_v256(get_field_by_symbol("sfIndexes"));
            for &offer_index in indexes.value() {
                if remaining == 0 {
                    break;
                }
                let offer_keylet = Keylet::new(LedgerEntryType::Offer, offer_index);
                let Ok(Some(offer_sle)) = ledger.read(offer_keylet) else {
                    continue;
                };

                let mut offer_json = offer_sle.json(JsonOptions::NONE);
                if let JsonValue::Object(ref mut offer_obj) = offer_json {
                    offer_obj.insert(
                        "index".to_owned(),
                        JsonValue::String(offer_index.to_string()),
                    );

                    // Compute quality from directory key (reference getQuality)
                    let quality_bytes = &next.data()[24..32];
                    let quality_u64 =
                        u64::from_be_bytes(quality_bytes.try_into().unwrap_or([0; 8]));
                    let dir_rate = protocol::amount_from_quality(quality_u64);
                    offer_obj.insert("quality".to_owned(), JsonValue::String(dir_rate.text()));

                    // Compute owner_funds: read owner's balance for the TakerGets asset.
                    let owner = offer_sle.get_account_id(get_field_by_symbol("sfAccount"));
                    let taker_gets = offer_sle.get_field_amount(get_field_by_symbol("sfTakerGets"));
                    let taker_pays = offer_sle.get_field_amount(get_field_by_symbol("sfTakerPays"));
                    let mut zero_out = taker_gets.clone();
                    zero_out.clear_with_asset(book.out);
                    let mut first_owner_offer = true;
                    let mut owner_funds = if book.out.issuer() == owner {
                        match book.out {
                            protocol::Asset::Issue(_) => taker_gets.clone(),
                            protocol::Asset::MPTIssue(issue) => {
                                if let Some(balance) = owner_balances.get(&owner) {
                                    first_owner_offer = false;
                                    balance.clone()
                                } else {
                                    ledger::mptoken_helpers::issuer_funds_to_self_issue(
                                        ledger.as_ref(),
                                        &issue,
                                    )
                                    .unwrap_or_else(|_| zero_out.clone())
                                }
                            }
                        }
                    } else if global_freeze {
                        zero_out.clone()
                    } else if let Some(balance) = owner_balances.get(&owner) {
                        first_owner_offer = false;
                        balance.clone()
                    } else {
                        let funds = ledger::account_funds(
                            ledger.as_ref(),
                            owner,
                            &taker_gets,
                            ledger::FreezeHandling::ZeroIfFrozen,
                        )
                        .unwrap_or_else(|_| zero_out.clone());
                        if funds < zero_out {
                            zero_out.clone()
                        } else {
                            funds
                        }
                    };

                    let owner_funds_before = owner_funds.clone();
                    let mut owner_funds_limit = owner_funds.clone();
                    let mut offer_rate = protocol::PARITY_RATE;
                    if transfer_rate != protocol::PARITY_RATE
                        && _taker != book.out.issuer()
                        && book.out.issuer() != owner
                    {
                        offer_rate = transfer_rate;
                        owner_funds_limit = protocol::divide_rate(&owner_funds, offer_rate);
                    }

                    let taker_gets_funded = if owner_funds_limit >= taker_gets {
                        taker_gets.clone()
                    } else {
                        offer_obj.insert(
                            "taker_gets_funded".to_owned(),
                            owner_funds_limit.json(JsonOptions::NONE),
                        );
                        let pays_funded = std::cmp::min(
                            taker_pays.clone(),
                            owner_funds_limit.multiply(&dir_rate, taker_pays.asset()),
                        );
                        offer_obj.insert(
                            "taker_pays_funded".to_owned(),
                            pays_funded.json(JsonOptions::NONE),
                        );
                        owner_funds_limit
                    };

                    let owner_pays = if offer_rate == protocol::PARITY_RATE {
                        taker_gets_funded.clone()
                    } else {
                        std::cmp::min(
                            owner_funds.clone(),
                            protocol::multiply_rate(&taker_gets_funded, offer_rate),
                        )
                    };
                    owner_funds -= owner_pays;
                    owner_balances.insert(owner, owner_funds.clone());

                    if first_owner_offer {
                        offer_obj.insert(
                            "owner_funds".to_owned(),
                            JsonValue::String(owner_funds_before.text()),
                        );
                    }
                }
                offers.push(offer_json);
                remaining -= 1;
            }

            tip_index = next;
        }

        obj.insert("offers".to_owned(), JsonValue::Array(offers));
    }
}

impl<V: AppServerInfoView + Sync> crate::handlers::ledger_data::LedgerDataSource
    for ApplicationServerInfo<V>
{
    fn resolve_ledger_data(
        &self,
        ledger: &LedgerLookupLedger,
        binary: bool,
        marker: Option<Uint256>,
        limit: i64,
        type_filter: LedgerEntryType,
    ) -> Result<crate::handlers::ledger_data::LedgerDataResolved, crate::status::RpcStatus> {
        let mut options = ledger::LedgerFillOptions::new(0);
        if binary {
            options |= ledger::LedgerFillOptions::BINARY;
        }
        let ledger_json = self.render_selected_ledger(*ledger, options)?;
        let mut entries = Vec::new();
        let remaining = limit;

        if resolve_lookup_ledger(&self.view, ledger).is_none() {
            return Err(crate::status::RpcStatus::new(
                crate::status::RpcErrorCode::LedgerNotFound,
            ));
        }
        // `doLedgerData` in rippled walks `sles.upperBound(marker)` and stops
        // before the first node beyond the requested page.  Do the same here.
        // Building an index/cache of every SLE before applying `limit` made a
        // cold `limit: 1` request scan and serialize the entire ledger.
        //
        // The page budget intentionally decrements *before* applying the type
        // filter.  That seemingly unusual ordering is rippled's observable
        // cursor contract: type-filtered queries advance through ledger keys,
        // not just matching entries.
        let mut cursor = marker.unwrap_or_default();
        let mut remaining = remaining;
        let mut next_marker = None;

        while let Some(next_key) = succ_lookup_ledger_key(&self.view, ledger, cursor, None) {
            let Some(sle) =
                read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(next_key))
            else {
                // A successor returned by a complete ledger must be readable.
                // Preserve the old tolerant behavior for a transient missing
                // node, but never advance past it: otherwise a page could
                // silently omit state.
                break;
            };

            if remaining <= 0 {
                let mut resume_before = next_key;
                resume_before.decrement();
                next_marker = Some(resume_before);
                break;
            }
            remaining -= 1;
            cursor = next_key;

            if type_filter != LedgerEntryType::Any && sle.get_type() != type_filter {
                continue;
            }

            let binary_data = if binary {
                let mut serializer = Serializer::new(256);
                sle.add(&mut serializer);
                Arc::<[u8]>::from(serializer.data().to_vec())
            } else {
                Arc::<[u8]>::from([])
            };
            let json = if binary {
                JsonValue::Null
            } else {
                sle.json(JsonOptions::NONE)
            };

            entries.push(crate::handlers::ledger_data::LedgerDataEntry {
                key: next_key,
                entry_type: sle.get_type(),
                json,
                binary: binary_data,
            });
        }

        Ok(crate::handlers::ledger_data::LedgerDataResolved {
            base_json: JsonValue::Object(BTreeMap::new()),
            ledger_json,
            entries,
            marker: next_marker,
            pre_rendered: None,
        })
    }
}

impl<V: AppServerInfoView> crate::state::feature::FeatureSource for ApplicationServerInfo<V> {
    fn feature_table_json(&self, is_admin: bool) -> JsonValue {
        self.view.amendment_status().feature_table_json(is_admin)
    }
    fn feature_json(&self, feature: Uint256, is_admin: bool) -> Option<JsonValue> {
        self.view.amendment_status().feature_json(feature, is_admin)
    }
    fn veto_feature(&self, feature: Uint256) {
        self.view
            .amendment_status()
            .set_vote(feature, app::AmendmentVote::Down);
    }
    fn unveto_feature(&self, feature: Uint256) {
        if let Some(registered) = protocol::registered_feature(&feature) {
            let vote = match registered.vote {
                protocol::RegisteredFeatureVote::DefaultYes => app::AmendmentVote::Up,
                protocol::RegisteredFeatureVote::DefaultNo => app::AmendmentVote::Down,
                protocol::RegisteredFeatureVote::Obsolete => app::AmendmentVote::Obsolete,
            };
            self.view.amendment_status().set_vote(feature, vote);
        }
    }
    fn majority_timestamps(&self) -> BTreeMap<Uint256, i64> {
        self.view.amendment_status().majority_timestamps()
    }
}

impl<V: AppServerInfoView> crate::commands::fetch_info::FetchInfoSource
    for ApplicationServerInfo<V>
{
    fn clear_ledger_fetch(&self) {
        if let Some(inbound) = self
            .view
            .app()
            .and_then(|app| app.ledger_master_runtime())
            .and_then(|runtime| runtime.inbound_ledgers.lock().ok()?.clone())
        {
            inbound.clear_failures();
        }
    }

    fn get_ledger_fetch_info(&self) -> JsonValue {
        self.view
            .app()
            .and_then(|app| app.ledger_master_runtime())
            .and_then(|runtime| runtime.inbound_ledgers.lock().ok()?.clone())
            .map(|inbound| inbound.fetch_info_bounded(16))
            .unwrap_or_else(|| JsonValue::Object(BTreeMap::new()))
    }
}

impl<V: AppServerInfoView> crate::amm::amm_info::AmmInfoSource for ApplicationServerInfo<V> {
    fn read_account_root(
        &self,
        ledger: &LedgerLookupLedger,
        account_id: AccountID,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(
            &self.view,
            ledger,
            account_keylet(Uint160::from_slice(account_id.data()).expect("account width")),
        )
    }
    fn read_ledger_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }

    fn parent_close_time(&self, ledger: &LedgerLookupLedger) -> u32 {
        if ledger.open {
            if let Some(open) = self.view.app().map(|app| app.open_ledger().current())
                && open.ledger_current_index == ledger.seq
                && open.close_time_resolution != 0
            {
                return open.parent_close_time;
            }

            // Bootstrap-only fallback for sources without a live ApplicationRoot.
            return [
                self.view.closed_ledger(),
                self.view.published_ledger(),
                self.view.validated_ledger(),
            ]
            .into_iter()
            .flatten()
            .filter(|candidate| candidate.header().seq.saturating_add(1) == ledger.seq)
            .max_by_key(|candidate| candidate.header().seq)
            .map(|parent| parent.header().close_time)
            .unwrap_or(0);
        }

        resolve_lookup_ledger(&self.view, ledger)
            .map(|resolved| resolved.header().parent_close_time)
            .unwrap_or(0)
    }
}

impl<V: AppServerInfoView> crate::handlers::vault_info::VaultInfoSource
    for ApplicationServerInfo<V>
{
    fn read_ledger_entry(
        &self,
        ledger: &LedgerLookupLedger,
        entry_index: Uint256,
    ) -> Option<STLedgerEntry> {
        read_lookup_ledger_entry(&self.view, ledger, unchecked_keylet(entry_index))
    }
}

impl<V: AppServerInfoView> crate::state::tx_reduce_relay::TxReduceRelaySource
    for ApplicationServerInfo<V>
{
    fn tx_metrics_json(&self) -> JsonValue {
        JsonValue::Object(BTreeMap::new())
    }
}

impl<V: AppServerInfoView> crate::handlers::get_aggregate_price::AggregatePriceSource
    for ApplicationServerInfo<V>
{
    fn read_oracle(
        &self,
        account: &str,
        document_id: u32,
    ) -> Option<crate::handlers::get_aggregate_price::OracleData> {
        let ledger = self
            .view
            .validated_ledger()
            .or_else(|| self.view.closed_ledger())?;
        let account_id = protocol::parse_base58_account_id(account)?;
        let keylet = protocol::oracle_keylet(Uint160::from_void(account_id.data()), document_id);
        let sle = ledger.read(keylet).ok().flatten()?;
        let last_update_time = sle.get_field_u32(protocol::get_field_by_symbol("sfLastUpdateTime"));
        let price_data_series_arr =
            sle.get_field_array(protocol::get_field_by_symbol("sfPriceDataSeries"));
        let mut entries = Vec::new();
        for entry in price_data_series_arr.iter() {
            let base_asset = protocol::currency_to_string(
                entry
                    .get_field_currency(protocol::get_field_by_symbol("sfBaseAsset"))
                    .currency(),
            );
            let quote_asset = protocol::currency_to_string(
                entry
                    .get_field_currency(protocol::get_field_by_symbol("sfQuoteAsset"))
                    .currency(),
            );
            let asset_price =
                if entry.is_field_present(protocol::get_field_by_symbol("sfAssetPrice")) {
                    Some(entry.get_field_u64(protocol::get_field_by_symbol("sfAssetPrice")))
                } else {
                    None
                };
            let scale = if entry.is_field_present(protocol::get_field_by_symbol("sfScale")) {
                entry.get_field_u8(protocol::get_field_by_symbol("sfScale"))
            } else {
                0
            };
            entries.push(crate::handlers::get_aggregate_price::PriceDataEntry {
                base_asset,
                quote_asset,
                asset_price,
                scale,
            });
        }
        Some(crate::handlers::get_aggregate_price::OracleData {
            last_update_time,
            price_data_series: entries,
        })
    }
}

impl<V: AppServerInfoView> crate::commands::black_list::BlackListSource
    for ApplicationServerInfo<V>
{
    fn black_list_json(&self) -> JsonValue {
        JsonValue::Object(BTreeMap::new())
    }

    fn black_list_json_with_threshold(&self, _threshold: i64) -> JsonValue {
        JsonValue::Object(BTreeMap::new())
    }
}
