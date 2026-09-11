use app::NodeFamily;
use basics::base_uint::Uint256;
use basics::tagged_cache::ManualClock;
use shamap::family::{FullBelowCache, NullMissingNodeReporter, NullNodeFetcher, SHAMapFamily};
use shamap::tree_node::SHAMapTreeNode;
use shamap::tree_node_cache::TreeNodeCache;
use std::sync::{Arc, Mutex};

#[derive(Debug, Default)]
struct RecordingFullBelowCache {
    generation: u32,
    inserted: Vec<Uint256>,
    sweeps: usize,
    clears: usize,
    resets: usize,
}

impl RecordingFullBelowCache {
    fn new(generation: u32) -> Self {
        Self {
            generation,
            ..Self::default()
        }
    }
}

#[derive(Debug, Clone)]
struct SharedFullBelowCache(Arc<Mutex<RecordingFullBelowCache>>);

impl FullBelowCache for SharedFullBelowCache {
    fn generation(&self) -> u32 {
        self.0
            .lock()
            .expect("full-below cache mutex must not be poisoned")
            .generation
    }

    fn touch_if_exists(&self, _hash: Uint256) -> bool {
        false
    }

    fn insert(&self, hash: Uint256) {
        self.0
            .lock()
            .expect("full-below cache mutex must not be poisoned")
            .inserted
            .push(hash);
    }

    fn sweep(&self) {
        self.0
            .lock()
            .expect("full-below cache mutex must not be poisoned")
            .sweeps += 1;
    }

    fn clear(&self) {
        let mut state = self
            .0
            .lock()
            .expect("full-below cache mutex must not be poisoned");
        state.clears += 1;
        state.inserted.clear();
        state.generation += 1;
    }

    fn reset(&self) {
        let mut state = self
            .0
            .lock()
            .expect("full-below cache mutex must not be poisoned");
        state.resets += 1;
        state.inserted.clear();
        state.generation = 1;
    }
}

#[test]
fn node_family_exposes_tree_node_cache_keys_without_mutating_cache_state() {
    let clock = Arc::new(ManualClock::new(0));
    let tree_cache = Arc::new(TreeNodeCache::new(
        "node-family-cache",
        8,
        time::Duration::seconds(1),
        Arc::clone(&clock),
    ));
    let full_below_state = Arc::new(Mutex::new(RecordingFullBelowCache::new(77)));
    let family = Arc::new(SHAMapFamily::new(
        Arc::clone(&tree_cache),
        SharedFullBelowCache(Arc::clone(&full_below_state)),
        NullNodeFetcher,
        NullMissingNodeReporter,
    ));
    let node_family = NodeFamily::from_arc(Arc::clone(&family));

    let first = Uint256::from_array([0x11; 32]);
    let second = Uint256::from_array([0x22; 32]);
    let mut first_node = SHAMapTreeNode::new_inner(1);
    tree_cache.canonicalize_replace_client(&first, &mut first_node);
    let mut second_node = SHAMapTreeNode::new_inner(1);
    tree_cache.canonicalize_replace_client(&second, &mut second_node);
    node_family.with_full_below_cache(|cache| cache.insert(first));

    let mut keys = node_family.tree_node_cache_keys();
    keys.sort_unstable();
    assert_eq!(keys, vec![first, second]);
    keys.clear();
    assert_eq!(node_family.tree_node_cache_keys().len(), 2);

    clock.advance_seconds(2);
    node_family.sweep();
    assert!(node_family.tree_node_cache_keys().is_empty());

    node_family.clear_full_below_cache();
    node_family.reset();

    let full_below = full_below_state
        .lock()
        .expect("full-below cache mutex must not be poisoned");
    assert_eq!(full_below.generation, 1);
    assert_eq!(full_below.inserted, Vec::<Uint256>::new());
    assert_eq!(full_below.sweeps, 1);
    assert_eq!(full_below.clears, 1);
    assert_eq!(full_below.resets, 1);
}
