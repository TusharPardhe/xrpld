use crate::{
    Backend, DatabaseImporter, DatabaseNodeImp, DatabaseRotatingImp, DatabaseSource, Factory,
    MemoryFactory, NodeObject, NodeStoreJournal, NuDbContext, NuDbFactory, NullFactory,
    RocksDbFactory, Scheduler,
};
use basics::basic_config::Section;
use std::any::Any;
use std::sync::{Arc, Mutex, OnceLock};

fn read_string(section: &Section, key: &str) -> String {
    section
        .get::<String>(key)
        .ok()
        .flatten()
        .unwrap_or_default()
}

fn clamp_read_threads(read_threads: i32) -> usize {
    read_threads.max(1) as usize
}

pub trait Manager: Send + Sync + 'static {
    fn insert(&self, factory: Arc<dyn Factory>);

    fn erase(&self, factory: &Arc<dyn Factory>);

    fn find(&self, name: &str) -> Option<Arc<dyn Factory>>;

    fn make_backend(
        &self,
        parameters: &Section,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Box<dyn Backend>, String>;

    fn make_backend_with_context(
        &self,
        parameters: &Section,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        context: &mut dyn Any,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Box<dyn Backend>, String>;

    fn make_backend_with_nudb_context(
        &self,
        parameters: &Section,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        context: &mut NuDbContext,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Box<dyn Backend>, String>;

    fn make_database(
        &self,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        read_threads: i32,
        config: &Section,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<DatabaseNodeImp>, String>;

    #[allow(clippy::too_many_arguments)]
    fn make_database_deterministic(
        &self,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        read_threads: i32,
        config: &Section,
        app_type: u64,
        uid: u64,
        salt: u64,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<DatabaseNodeImp>, String>;

    #[allow(clippy::too_many_arguments)]
    fn make_database_with_context(
        &self,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        read_threads: i32,
        config: &Section,
        context: &mut dyn Any,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<DatabaseNodeImp>, String>;

    fn make_database_with_nudb_context(
        &self,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        read_threads: i32,
        config: &Section,
        context: &mut NuDbContext,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<DatabaseNodeImp>, String>;

    #[allow(clippy::too_many_arguments)]
    fn make_rotating_database(
        &self,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        read_threads: i32,
        writable_backend_config: &Section,
        archive_backend_config: &Section,
        database_config: &Section,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<DatabaseRotatingImp>, String>;

    fn import(&self, destination: &dyn DatabaseImporter, source: &dyn DatabaseSource);

    fn export(&self, source: &dyn DatabaseSource) -> Vec<Arc<NodeObject>>;

    fn visit(&self, source: &dyn DatabaseSource, callback: &mut dyn FnMut(Arc<NodeObject>));
}

impl dyn Manager {
    pub fn instance() -> &'static ManagerImp {
        ManagerImp::instance()
    }
}

pub struct ManagerImp {
    factories: Mutex<Vec<Arc<dyn Factory>>>,
}

impl ManagerImp {
    pub fn new() -> Self {
        let manager = Self {
            factories: Mutex::new(Vec::new()),
        };
        manager.insert(Arc::new(RocksDbFactory::new()));
        manager.insert(Arc::new(NuDbFactory::new()));
        manager.insert(Arc::new(NullFactory::new()));
        manager.insert(Arc::new(MemoryFactory::new()));
        manager
    }

    pub fn instance() -> &'static Self {
        static INSTANCE: OnceLock<ManagerImp> = OnceLock::new();
        INSTANCE.get_or_init(Self::new)
    }

    pub fn missing_backend() -> String {
        "Your quaxar.cfg is missing a [node_db] entry; please see the Quaxar example configuration"
            .to_owned()
    }
}

impl Default for ManagerImp {
    fn default() -> Self {
        Self::new()
    }
}

impl Manager for ManagerImp {
    fn insert(&self, factory: Arc<dyn Factory>) {
        self.factories
            .lock()
            .expect("node store manager factories mutex must not be poisoned")
            .push(factory);
    }

    fn erase(&self, factory: &Arc<dyn Factory>) {
        let mut factories = self
            .factories
            .lock()
            .expect("node store manager factories mutex must not be poisoned");
        let index = factories
            .iter()
            .position(|other| Arc::ptr_eq(other, factory))
            .expect("xrpl::NodeStore::ManagerImp::erase : valid input");
        factories.remove(index);
    }

    fn find(&self, name: &str) -> Option<Arc<dyn Factory>> {
        let factories = self
            .factories
            .lock()
            .expect("node store manager factories mutex must not be poisoned");
        factories
            .iter()
            .find(|factory| factory.get_name().eq_ignore_ascii_case(name))
            .cloned()
    }

    fn make_backend(
        &self,
        parameters: &Section,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Box<dyn Backend>, String> {
        let backend_type = read_string(parameters, "type");
        if backend_type.is_empty() {
            return Err(Self::missing_backend());
        }

        let Some(factory) = self.find(&backend_type) else {
            return Err(Self::missing_backend());
        };

        factory.create_instance(
            NodeObject::KEY_BYTES,
            parameters,
            burst_size,
            scheduler,
            journal,
        )
    }

    fn make_backend_with_nudb_context(
        &self,
        parameters: &Section,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        context: &mut NuDbContext,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Box<dyn Backend>, String> {
        let backend_type = read_string(parameters, "type");
        if backend_type.is_empty() {
            return Err(Self::missing_backend());
        }

        let Some(factory) = self.find(&backend_type) else {
            return Err(Self::missing_backend());
        };

        if let Some(result) = factory.create_instance_with_nudb_context(
            NodeObject::KEY_BYTES,
            parameters,
            burst_size,
            Arc::clone(&scheduler),
            context,
            Arc::clone(&journal),
        ) {
            return result;
        }

        factory.create_instance(
            NodeObject::KEY_BYTES,
            parameters,
            burst_size,
            scheduler,
            journal,
        )
    }

    fn make_backend_with_context(
        &self,
        parameters: &Section,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        context: &mut dyn Any,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Box<dyn Backend>, String> {
        let backend_type = read_string(parameters, "type");
        if backend_type.is_empty() {
            return Err(Self::missing_backend());
        }

        let Some(factory) = self.find(&backend_type) else {
            return Err(Self::missing_backend());
        };

        if let Some(result) = factory.create_instance_with_context(
            NodeObject::KEY_BYTES,
            parameters,
            burst_size,
            Arc::clone(&scheduler),
            context,
            Arc::clone(&journal),
        ) {
            return result;
        }

        factory.create_instance(
            NodeObject::KEY_BYTES,
            parameters,
            burst_size,
            scheduler,
            journal,
        )
    }

    fn make_database(
        &self,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        read_threads: i32,
        config: &Section,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<DatabaseNodeImp>, String> {
        let read_threads = clamp_read_threads(read_threads);
        let backend = self.make_backend(
            config,
            burst_size,
            Arc::clone(&scheduler),
            Arc::clone(&journal),
        )?;
        backend.open(true)?;
        let backend: Arc<dyn Backend> = backend.into();
        DatabaseNodeImp::new(scheduler, read_threads, backend, config, journal)
    }

    fn make_database_deterministic(
        &self,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        read_threads: i32,
        config: &Section,
        app_type: u64,
        uid: u64,
        salt: u64,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<DatabaseNodeImp>, String> {
        let read_threads = clamp_read_threads(read_threads);
        let backend = self.make_backend(
            config,
            burst_size,
            Arc::clone(&scheduler),
            Arc::clone(&journal),
        )?;
        backend.open_deterministic(true, app_type, uid, salt)?;
        let backend: Arc<dyn Backend> = backend.into();
        DatabaseNodeImp::new(scheduler, read_threads, backend, config, journal)
    }

    fn make_database_with_context(
        &self,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        read_threads: i32,
        config: &Section,
        context: &mut dyn Any,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<DatabaseNodeImp>, String> {
        let read_threads = clamp_read_threads(read_threads);
        let backend = self.make_backend_with_context(
            config,
            burst_size,
            Arc::clone(&scheduler),
            context,
            Arc::clone(&journal),
        )?;
        backend.open(true)?;
        let backend: Arc<dyn Backend> = backend.into();
        DatabaseNodeImp::new(scheduler, read_threads, backend, config, journal)
    }

    fn make_database_with_nudb_context(
        &self,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        read_threads: i32,
        config: &Section,
        context: &mut NuDbContext,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<DatabaseNodeImp>, String> {
        let read_threads = clamp_read_threads(read_threads);
        let backend = self.make_backend_with_nudb_context(
            config,
            burst_size,
            Arc::clone(&scheduler),
            context,
            Arc::clone(&journal),
        )?;
        backend.open(true)?;
        let backend: Arc<dyn Backend> = backend.into();
        DatabaseNodeImp::new(scheduler, read_threads, backend, config, journal)
    }

    #[allow(clippy::too_many_arguments)]
    fn make_rotating_database(
        &self,
        burst_size: usize,
        scheduler: Arc<dyn Scheduler>,
        read_threads: i32,
        writable_backend_config: &Section,
        archive_backend_config: &Section,
        database_config: &Section,
        journal: Arc<dyn NodeStoreJournal>,
    ) -> Result<Arc<DatabaseRotatingImp>, String> {
        let read_threads = clamp_read_threads(read_threads);
        let writable_backend = self.make_backend(
            writable_backend_config,
            burst_size,
            Arc::clone(&scheduler),
            Arc::clone(&journal),
        )?;
        writable_backend.open(true)?;

        let archive_backend = self.make_backend(
            archive_backend_config,
            burst_size,
            Arc::clone(&scheduler),
            Arc::clone(&journal),
        )?;
        archive_backend.open(true)?;

        let writable_backend: Arc<dyn Backend> = writable_backend.into();
        let archive_backend: Arc<dyn Backend> = archive_backend.into();

        DatabaseRotatingImp::new(
            scheduler,
            read_threads,
            writable_backend,
            archive_backend,
            database_config,
            journal,
        )
    }

    fn import(&self, destination: &dyn DatabaseImporter, source: &dyn DatabaseSource) {
        destination.import_database(source);
    }

    fn export(&self, source: &dyn DatabaseSource) -> Vec<Arc<NodeObject>> {
        let mut exported = Vec::new();
        self.visit(source, &mut |node_object| exported.push(node_object));
        exported
    }

    fn visit(&self, source: &dyn DatabaseSource, callback: &mut dyn FnMut(Arc<NodeObject>)) {
        source.for_each(callback);
    }
}

#[cfg(test)]
mod tests {
    use super::{Manager, ManagerImp};
    use crate::database::{DatabaseImporter, DatabaseSource};
    use crate::{
        Backend, Factory, NodeObject, NodeStoreJournal, NuDbContext, NullJournal, Scheduler, Status,
    };
    use basics::{base_uint::Uint256, basic_config::Section};
    use protocol::JsonValue;
    use std::any::Any;
    use std::collections::BTreeMap;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};

    struct TestBackend(&'static str);

    impl Backend for TestBackend {
        fn get_name(&self) -> String {
            self.0.to_owned()
        }

        fn open(&self, _create_if_missing: bool) -> Result<(), String> {
            Ok(())
        }

        fn is_open(&self) -> bool {
            true
        }

        fn close(&self) -> Result<(), String> {
            Ok(())
        }

        fn fetch(&self, _hash: &Uint256) -> (Option<Arc<NodeObject>>, Status) {
            (None, Status::NotFound)
        }

        fn fetch_batch(&self, _hashes: &[Uint256]) -> (Vec<Option<Arc<NodeObject>>>, Status) {
            (Vec::new(), Status::Ok)
        }

        fn store(&self, _object: Arc<NodeObject>) -> Result<(), String> {
            Ok(())
        }

        fn store_batch(&self, _batch: &crate::Batch) {}

        fn sync(&self) {}

        fn for_each(&self, _callback: &mut dyn FnMut(Arc<NodeObject>)) {}

        fn get_write_load(&self) -> i32 {
            0
        }

        fn set_delete_path(&self) {}

        fn fd_required(&self) -> i32 {
            0
        }
    }

    struct DeterministicBackend {
        opened: Arc<AtomicBool>,
        app_type: Arc<AtomicU64>,
        uid: Arc<AtomicU64>,
        salt: Arc<AtomicU64>,
    }

    impl Backend for DeterministicBackend {
        fn get_name(&self) -> String {
            "deterministic".to_owned()
        }

        fn open(&self, _create_if_missing: bool) -> Result<(), String> {
            self.opened.store(true, Ordering::Relaxed);
            Ok(())
        }

        fn open_deterministic(
            &self,
            _create_if_missing: bool,
            app_type: u64,
            uid: u64,
            salt: u64,
        ) -> Result<(), String> {
            self.opened.store(true, Ordering::Relaxed);
            self.app_type.store(app_type, Ordering::Relaxed);
            self.uid.store(uid, Ordering::Relaxed);
            self.salt.store(salt, Ordering::Relaxed);
            Ok(())
        }

        fn is_open(&self) -> bool {
            self.opened.load(Ordering::Relaxed)
        }

        fn close(&self) -> Result<(), String> {
            self.opened.store(false, Ordering::Relaxed);
            Ok(())
        }

        fn fetch(&self, _hash: &Uint256) -> (Option<Arc<NodeObject>>, Status) {
            (None, Status::NotFound)
        }

        fn fetch_batch(&self, _hashes: &[Uint256]) -> (Vec<Option<Arc<NodeObject>>>, Status) {
            (Vec::new(), Status::Ok)
        }

        fn store(&self, _object: Arc<NodeObject>) -> Result<(), String> {
            Ok(())
        }

        fn store_batch(&self, _batch: &crate::Batch) {}

        fn sync(&self) {}

        fn for_each(&self, _callback: &mut dyn FnMut(Arc<NodeObject>)) {}

        fn get_write_load(&self) -> i32 {
            0
        }

        fn set_delete_path(&self) {}

        fn fd_required(&self) -> i32 {
            0
        }
    }

    struct TestFactory {
        name: &'static str,
        backend_name: &'static str,
    }

    impl Factory for TestFactory {
        fn get_name(&self) -> String {
            self.name.to_owned()
        }

        fn create_instance(
            &self,
            _key_bytes: usize,
            _parameters: &Section,
            _burst_size: usize,
            _scheduler: Arc<dyn Scheduler>,
            _journal: Arc<dyn NodeStoreJournal>,
        ) -> crate::factory::BackendResult {
            Ok(Box::new(TestBackend(self.backend_name)))
        }
    }

    struct ContextFactory {
        context_supported: bool,
        context_seen: Arc<AtomicBool>,
        deterministic_opened: Arc<AtomicBool>,
        app_type: Arc<AtomicU64>,
        uid: Arc<AtomicU64>,
        salt: Arc<AtomicU64>,
    }

    impl Factory for ContextFactory {
        fn get_name(&self) -> String {
            "Context".to_owned()
        }

        fn create_instance(
            &self,
            _key_bytes: usize,
            _parameters: &Section,
            _burst_size: usize,
            _scheduler: Arc<dyn Scheduler>,
            _journal: Arc<dyn NodeStoreJournal>,
        ) -> crate::factory::BackendResult {
            Ok(Box::new(DeterministicBackend {
                opened: Arc::clone(&self.deterministic_opened),
                app_type: Arc::clone(&self.app_type),
                uid: Arc::clone(&self.uid),
                salt: Arc::clone(&self.salt),
            }))
        }

        fn create_instance_with_context(
            &self,
            _key_bytes: usize,
            _parameters: &Section,
            _burst_size: usize,
            _scheduler: Arc<dyn Scheduler>,
            context: &mut dyn Any,
            _journal: Arc<dyn NodeStoreJournal>,
        ) -> Option<crate::factory::BackendResult> {
            if !self.context_supported {
                return None;
            }

            let marker = context
                .downcast_mut::<bool>()
                .expect("test context should be bool");
            *marker = true;
            self.context_seen.store(true, Ordering::Relaxed);

            Some(self.create_instance(
                0,
                &Section::new("node_db"),
                0,
                Arc::new(crate::DummyScheduler),
                Arc::new(NullJournal),
            ))
        }

        fn create_instance_with_nudb_context(
            &self,
            _key_bytes: usize,
            _parameters: &Section,
            _burst_size: usize,
            _scheduler: Arc<dyn Scheduler>,
            context: &mut NuDbContext,
            _journal: Arc<dyn NodeStoreJournal>,
        ) -> Option<crate::factory::BackendResult> {
            if !self.context_supported {
                return None;
            }

            *context = NuDbContext::new(17, 19, 23);
            self.context_seen.store(true, Ordering::Relaxed);

            Some(self.create_instance(
                0,
                &Section::new("node_db"),
                0,
                Arc::new(crate::DummyScheduler),
                Arc::new(NullJournal),
            ))
        }
    }

    #[derive(Default)]
    struct TestSource {
        objects: Vec<Arc<NodeObject>>,
    }

    impl DatabaseSource for TestSource {
        fn for_each(&self, callback: &mut dyn FnMut(Arc<NodeObject>)) {
            for object in &self.objects {
                callback(Arc::clone(object));
            }
        }
    }

    #[derive(Default)]
    struct CollectingImporter {
        objects: std::sync::Mutex<BTreeMap<Uint256, Arc<NodeObject>>>,
    }

    impl DatabaseImporter for CollectingImporter {
        fn import_database(&self, source: &dyn DatabaseSource) {
            source.for_each(&mut |object| {
                self.objects
                    .lock()
                    .expect("test importer mutex must not be poisoned")
                    .insert(*object.hash(), object);
            });
        }
    }

    fn section(backend_type: &str) -> Section {
        let mut section = Section::new("node_db");
        section.set("type", backend_type);
        section
    }

    #[test]
    fn manager_find_is_case_insensitive_and_registers_memory_by_default() {
        let manager = ManagerImp::new();
        assert!(manager.find("memory").is_some());
        assert!(manager.find("MeMoRy").is_some());
        assert!(manager.find("none").is_some());
        assert!(manager.find("nudb").is_some());
        assert!(manager.find("rocksdb").is_some());
    }

    #[test]
    fn manager_insert_preserves_duplicate_first_match_semantics() {
        let manager = ManagerImp {
            factories: std::sync::Mutex::new(Vec::new()),
        };
        let first: Arc<dyn Factory> = Arc::new(TestFactory {
            name: "Dup",
            backend_name: "first",
        });
        let second: Arc<dyn Factory> = Arc::new(TestFactory {
            name: "dup",
            backend_name: "second",
        });

        manager.insert(Arc::clone(&first));
        manager.insert(Arc::clone(&second));

        let backend = manager
            .make_backend(
                &section("DUP"),
                0,
                Arc::new(crate::DummyScheduler),
                Arc::new(NullJournal),
            )
            .expect("factory lookup should succeed");
        assert_eq!(backend.get_name(), "first");
    }

    #[test]
    fn manager_erase_removes_only_first_matching_pointer() {
        let manager = ManagerImp {
            factories: std::sync::Mutex::new(Vec::new()),
        };
        let factory: Arc<dyn Factory> = Arc::new(TestFactory {
            name: "Dup",
            backend_name: "first",
        });

        manager.insert(Arc::clone(&factory));
        manager.insert(Arc::clone(&factory));
        manager.erase(&factory);

        let factories = manager
            .factories
            .lock()
            .expect("node store manager factories mutex must not be poisoned");
        assert_eq!(factories.len(), 1);
        assert!(Arc::ptr_eq(&factories[0], &factory));
    }

    #[test]
    fn manager_make_backend_uses_cpp_missing_backend_error() {
        let manager = ManagerImp {
            factories: std::sync::Mutex::new(Vec::new()),
        };

        let missing_type = manager.make_backend(
            &Section::new("node_db"),
            0,
            Arc::new(crate::DummyScheduler),
            Arc::new(NullJournal),
        );
        match missing_type {
            Ok(_) => panic!("backend construction should fail without a type"),
            Err(error) => assert_eq!(error, ManagerImp::missing_backend()),
        }

        let unknown = manager.make_backend(
            &section("unknown"),
            0,
            Arc::new(crate::DummyScheduler),
            Arc::new(NullJournal),
        );
        match unknown {
            Ok(_) => panic!("backend construction should fail for an unknown type"),
            Err(error) => assert_eq!(error, ManagerImp::missing_backend()),
        }
    }

    #[test]
    fn manager_can_construct_rotating_memory_database() {
        let manager = ManagerImp::new();
        let mut writable = section("memory");
        writable.set("path", "writable");
        let mut archive = section("memory");
        archive.set("path", "archive");

        let database = manager
            .make_rotating_database(
                0,
                Arc::new(crate::DummyScheduler),
                1,
                &writable,
                &archive,
                &writable,
                Arc::new(NullJournal),
            )
            .expect("rotating database");

        assert_eq!(database.get_name(), "writable");
        assert_eq!(database.fd_required(), 0);
        database.stop();
    }

    #[test]
    fn manager_clamps_non_positive_read_threads_before_constructing_databases() {
        let manager = ManagerImp::new();
        let scheduler: Arc<dyn Scheduler> = Arc::new(crate::DummyScheduler);
        let journal: Arc<dyn NodeStoreJournal> = Arc::new(NullJournal);

        let mut zero_config = section("memory");
        zero_config.set("path", "validation-zero");
        let zero_threads = manager.make_database(
            0,
            Arc::clone(&scheduler),
            0,
            &zero_config,
            Arc::clone(&journal),
        );
        let zero_threads = zero_threads.expect("zero read threads should clamp to one");
        let JsonValue::Object(zero_counts) = zero_threads.get_counts_json() else {
            panic!("database counts should be a JSON object");
        };
        assert_eq!(
            zero_counts.get("read_threads_total"),
            Some(&JsonValue::Signed(1))
        );
        zero_threads.stop();

        let mut negative_config = section("memory");
        negative_config.set("path", "validation-negative");
        let negative_threads = manager.make_database(
            0,
            Arc::clone(&scheduler),
            -1,
            &negative_config,
            Arc::clone(&journal),
        );
        let negative_threads = negative_threads.expect("negative read threads should clamp to one");
        let JsonValue::Object(negative_counts) = negative_threads.get_counts_json() else {
            panic!("database counts should be a JSON object");
        };
        assert_eq!(
            negative_counts.get("read_threads_total"),
            Some(&JsonValue::Signed(1))
        );
        negative_threads.stop();

        let mut writable = section("memory");
        writable.set("path", "writable");
        let mut archive = section("memory");
        archive.set("path", "archive");
        let rotating = manager
            .make_rotating_database(
                0,
                Arc::clone(&scheduler),
                0,
                &writable,
                &archive,
                &writable,
                journal,
            )
            .expect("rotating zero read threads should clamp to one");
        let JsonValue::Object(rotating_counts) = rotating.get_counts_json() else {
            panic!("database counts should be a JSON object");
        };
        assert_eq!(
            rotating_counts.get("read_threads_total"),
            Some(&JsonValue::Signed(1))
        );
        rotating.stop();
    }

    #[test]
    fn manager_make_backend_with_context_prefers_factory_context_path_and_falls_back() {
        let manager = ManagerImp {
            factories: std::sync::Mutex::new(Vec::new()),
        };
        let context_seen = Arc::new(AtomicBool::new(false));
        let deterministic_opened = Arc::new(AtomicBool::new(false));
        let app_type = Arc::new(AtomicU64::new(0));
        let uid = Arc::new(AtomicU64::new(0));
        let salt = Arc::new(AtomicU64::new(0));

        manager.insert(Arc::new(ContextFactory {
            context_supported: true,
            context_seen: Arc::clone(&context_seen),
            deterministic_opened: Arc::clone(&deterministic_opened),
            app_type: Arc::clone(&app_type),
            uid: Arc::clone(&uid),
            salt: Arc::clone(&salt),
        }));

        let mut config = section("context");
        let mut marker = false;
        let backend = manager
            .make_backend_with_context(
                &config,
                0,
                Arc::new(crate::DummyScheduler),
                &mut marker,
                Arc::new(NullJournal),
            )
            .expect("context backend");
        assert_eq!(backend.get_name(), "deterministic");
        assert!(marker);
        assert!(context_seen.load(Ordering::Relaxed));

        let fallback_manager = ManagerImp {
            factories: std::sync::Mutex::new(Vec::new()),
        };
        fallback_manager.insert(Arc::new(ContextFactory {
            context_supported: false,
            context_seen: Arc::new(AtomicBool::new(false)),
            deterministic_opened: Arc::new(AtomicBool::new(false)),
            app_type: Arc::new(AtomicU64::new(0)),
            uid: Arc::new(AtomicU64::new(0)),
            salt: Arc::new(AtomicU64::new(0)),
        }));
        config.set("type", "context");
        let mut fallback_marker = false;
        let backend = fallback_manager
            .make_backend_with_context(
                &config,
                0,
                Arc::new(crate::DummyScheduler),
                &mut fallback_marker,
                Arc::new(NullJournal),
            )
            .expect("fallback backend");
        assert_eq!(backend.get_name(), "deterministic");
        assert!(!fallback_marker);
    }

    #[test]
    fn manager_make_database_deterministic_preserves_backend_open_arguments() {
        let manager = ManagerImp {
            factories: std::sync::Mutex::new(Vec::new()),
        };
        let deterministic_opened = Arc::new(AtomicBool::new(false));
        let app_type = Arc::new(AtomicU64::new(0));
        let uid = Arc::new(AtomicU64::new(0));
        let salt = Arc::new(AtomicU64::new(0));

        manager.insert(Arc::new(ContextFactory {
            context_supported: false,
            context_seen: Arc::new(AtomicBool::new(false)),
            deterministic_opened: Arc::clone(&deterministic_opened),
            app_type: Arc::clone(&app_type),
            uid: Arc::clone(&uid),
            salt: Arc::clone(&salt),
        }));

        let config = section("context");
        let database = manager
            .make_database_deterministic(
                0,
                Arc::new(crate::DummyScheduler),
                1,
                &config,
                7,
                11,
                13,
                Arc::new(NullJournal),
            )
            .expect("deterministic database");

        assert!(deterministic_opened.load(Ordering::Relaxed));
        assert_eq!(app_type.load(Ordering::Relaxed), 7);
        assert_eq!(uid.load(Ordering::Relaxed), 11);
        assert_eq!(salt.load(Ordering::Relaxed), 13);
        database.stop();
    }

    #[test]
    fn manager_make_backend_with_typed_nudb_context_prefers_typed_factory_path() {
        let manager = ManagerImp {
            factories: std::sync::Mutex::new(Vec::new()),
        };
        let context_seen = Arc::new(AtomicBool::new(false));

        manager.insert(Arc::new(ContextFactory {
            context_supported: true,
            context_seen: Arc::clone(&context_seen),
            deterministic_opened: Arc::new(AtomicBool::new(false)),
            app_type: Arc::new(AtomicU64::new(0)),
            uid: Arc::new(AtomicU64::new(0)),
            salt: Arc::new(AtomicU64::new(0)),
        }));

        let config = section("context");
        let mut context = NuDbContext::new(1, 2, 3);
        let backend = manager
            .make_backend_with_nudb_context(
                &config,
                0,
                Arc::new(crate::DummyScheduler),
                &mut context,
                Arc::new(NullJournal),
            )
            .expect("typed NuDB context backend");

        assert_eq!(backend.get_name(), "deterministic");
        assert!(context_seen.load(Ordering::Relaxed));
        assert_eq!(context, NuDbContext::new(17, 19, 23));
    }

    #[test]
    fn manager_visit_and_export_preserve_database_source_iteration() {
        let manager = ManagerImp::new();
        let first = Arc::new(NodeObject::new(
            crate::NodeObjectType::Ledger,
            vec![1, 2, 3],
            Uint256::from_array([0x11; 32]),
        ));
        let second = Arc::new(NodeObject::new(
            crate::NodeObjectType::TransactionNode,
            vec![4, 5, 6, 7],
            Uint256::from_array([0x22; 32]),
        ));
        let source = TestSource {
            objects: vec![Arc::clone(&first), Arc::clone(&second)],
        };

        let mut visited = Vec::new();
        manager.visit(&source, &mut |object| visited.push(*object.hash()));
        assert_eq!(visited, vec![*first.hash(), *second.hash()]);

        let exported = manager.export(&source);
        assert_eq!(exported.len(), 2);
        assert_eq!(exported[0].data(), first.data());
        assert_eq!(exported[1].data(), second.data());
    }

    #[test]
    fn manager_import_replays_exported_objects_into_destination() {
        let manager = ManagerImp::new();
        let source = TestSource {
            objects: vec![
                Arc::new(NodeObject::new(
                    crate::NodeObjectType::Ledger,
                    vec![9, 8, 7],
                    Uint256::from_array([0x33; 32]),
                )),
                Arc::new(NodeObject::new(
                    crate::NodeObjectType::TransactionNode,
                    vec![6, 5, 4, 3],
                    Uint256::from_array([0x44; 32]),
                )),
            ],
        };
        let destination = CollectingImporter::default();

        manager.import(&destination, &source);

        let imported = destination
            .objects
            .lock()
            .expect("test importer mutex must not be poisoned");
        assert_eq!(imported.len(), 2);
        assert_eq!(
            imported
                .get(&Uint256::from_array([0x33; 32]))
                .expect("first object imported")
                .data(),
            &[9, 8, 7]
        );
        assert_eq!(
            imported
                .get(&Uint256::from_array([0x44; 32]))
                .expect("second object imported")
                .data(),
            &[6, 5, 4, 3]
        );
    }
}
