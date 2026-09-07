use crate::shamap::shamap_store_paths::SHAMAP_STORE_DB_PREFIX;
use crate::{SHAMapStorePathPlan, SHAMapStoreSavedState, reconcile_shamap_store_paths};
use basics::basic_config::Section;
use nodestore::{
    Backend, Database, DatabaseRotating, DatabaseRotatingImp, Manager, NodeStoreJournal, Scheduler,
};
use std::path::PathBuf;
use std::sync::Arc;

#[derive(Clone)]
pub enum SHAMapStoreNodeStore {
    Single(Arc<dyn Database>),
    Rotating(Arc<dyn DatabaseRotating>),
}

impl SHAMapStoreNodeStore {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Single(_) => "single",
            Self::Rotating(_) => "rotating",
        }
    }

    pub fn fd_required(&self) -> i32 {
        match self {
            Self::Single(database) => database.fd_required(),
            Self::Rotating(database) => database.fd_required(),
        }
    }

    /// Stable nonzero NodeStore generation observed by local-read admission.
    /// Rotating stores advance it before cache invalidation/copy-forward;
    /// callers must include it in `ReadKey` and durable callback identities.
    pub fn store_generation(&self) -> u64 {
        match self {
            Self::Single(database) => database.store_generation(),
            Self::Rotating(database) => database.store_generation(),
        }
    }

    pub fn schedule_write(&self, write: nodestore::ScheduledWrite) {
        match self {
            Self::Single(database) => database.schedule_write(write),
            Self::Rotating(database) => database.schedule_write(write),
        }
    }

    pub fn export_backend(&self) -> Option<Arc<dyn Backend>> {
        match self {
            Self::Single(database) => database.export_backend(),
            Self::Rotating(database) => database.export_backend(),
        }
    }

    /// Evicts an in-memory membership (Bloom) filter to reclaim RAM once a
    /// transient backfill accelerator is no longer needed. Single stores free
    /// the filter; rotating stores keep theirs (the rotating implementation
    /// overrides this to a no-op) because they need it for steady-state
    /// cross-store probe skipping.
    pub fn evict_membership_filter(&self) {
        match self {
            Self::Single(database) => database.evict_membership_filter(),
            Self::Rotating(database) => database.evict_membership_filter(),
        }
    }
}

pub struct SHAMapStoreBackendBundle {
    pub store: SHAMapStoreNodeStore,
    pub fd_required: i32,
    pub saved_state: SHAMapStoreSavedState,
}

impl SHAMapStoreBackendBundle {
    pub fn node_store_kind(&self) -> &'static str {
        self.store.kind()
    }
}

pub fn apply_rocksdb_online_delete_defaults(
    node_db: &Section,
    hash_node_db_cache_mb: usize,
    node_size: u32,
) -> Section {
    let mut section = node_db.clone();
    let backend_type = section
        .get::<String>("type")
        .ok()
        .flatten()
        .unwrap_or_default();
    if backend_type.eq_ignore_ascii_case("RocksDB") {
        if !section.exists("cache_mb") {
            section.set("cache_mb", hash_node_db_cache_mb.to_string());
        }
        if !section.exists("filter_bits") && node_size >= 2 {
            section.set("filter_bits", "10");
        }
    }
    section
}

pub fn make_shamap_store_backend(
    manager: &dyn Manager,
    scheduler: Arc<dyn Scheduler>,
    read_threads: i32,
    node_db: &Section,
    delete_interval: u32,
    state: &SHAMapStoreSavedState,
    burst_size: usize,
    journal: Arc<dyn NodeStoreJournal>,
) -> Result<SHAMapStoreBackendBundle, String> {
    if delete_interval == 0 {
        let database = manager.make_database(
            burst_size,
            scheduler,
            read_threads,
            node_db,
            Arc::clone(&journal),
        )?;
        let fd_required = database.fd_required();
        return Ok(SHAMapStoreBackendBundle {
            store: SHAMapStoreNodeStore::Single(database),
            fd_required,
            saved_state: state.clone(),
        });
    }

    let path_plan = reconcile_shamap_store_paths(node_db, state)?;
    make_rotating_from_plan(
        manager,
        scheduler,
        read_threads,
        node_db,
        path_plan,
        burst_size,
        journal,
    )
}

pub fn make_shamap_store_rotating_backend(
    manager: &dyn Manager,
    node_db: &Section,
    burst_size: usize,
    scheduler: Arc<dyn Scheduler>,
    journal: Arc<dyn NodeStoreJournal>,
    path: Option<&str>,
) -> Result<Box<dyn Backend>, String> {
    let mut section = node_db.clone();
    let resolved_path = match path {
        Some(path) => path.to_owned(),
        None => unique_backend_path(node_db)?,
    };
    section.set("path", resolved_path);
    let backend = manager.make_backend(&section, burst_size, scheduler, journal)?;
    backend.open(true)?;
    Ok(backend)
}

fn make_rotating_from_plan(
    manager: &dyn Manager,
    scheduler: Arc<dyn Scheduler>,
    read_threads: i32,
    node_db: &Section,
    mut path_plan: SHAMapStorePathPlan,
    burst_size: usize,
    journal: Arc<dyn NodeStoreJournal>,
) -> Result<SHAMapStoreBackendBundle, String> {
    if path_plan.state.writable_db.is_empty() {
        let mut reserved = path_plan.stale_paths.clone();
        let writable_path = unique_backend_path_excluding(node_db, &reserved)?;
        reserved.push(PathBuf::from(&writable_path));
        let archive_path = unique_backend_path_excluding(node_db, &reserved)?;
        path_plan.state.writable_db = writable_path;
        path_plan.state.archive_db = archive_path;
    }

    path_plan.cleanup_stale_paths()?;

    let writable = make_shamap_store_rotating_backend(
        manager,
        node_db,
        burst_size,
        Arc::clone(&scheduler),
        Arc::clone(&journal),
        (!path_plan.state.writable_db.is_empty()).then_some(path_plan.state.writable_db.as_str()),
    )?;
    let archive = make_shamap_store_rotating_backend(
        manager,
        node_db,
        burst_size,
        Arc::clone(&scheduler),
        Arc::clone(&journal),
        (!path_plan.state.archive_db.is_empty()).then_some(path_plan.state.archive_db.as_str()),
    )?;

    let rotating = DatabaseRotatingImp::new(
        scheduler,
        read_threads as usize,
        Arc::from(writable),
        Arc::from(archive),
        node_db,
        journal,
    )?;
    let fd_required = rotating.fd_required();

    Ok(SHAMapStoreBackendBundle {
        store: SHAMapStoreNodeStore::Rotating(rotating),
        fd_required,
        saved_state: path_plan.state,
    })
}

fn unique_backend_path(node_db: &Section) -> Result<String, String> {
    unique_backend_path_excluding(node_db, &[])
}

fn unique_backend_path_excluding(
    node_db: &Section,
    reserved: &[PathBuf],
) -> Result<String, String> {
    let base = PathBuf::from(
        node_db
            .get::<String>("path")
            .ok()
            .flatten()
            .unwrap_or_default(),
    );
    for suffix in 0..10_000_u32 {
        let candidate = base.join(format!("{SHAMAP_STORE_DB_PREFIX}.{suffix:04}"));
        if !candidate.exists() && !reserved.iter().any(|path| path == &candidate) {
            return Ok(candidate.to_string_lossy().into_owned());
        }
    }
    Err("Unable to allocate a unique rotating backend path".to_owned())
}
