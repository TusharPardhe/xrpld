use basics::intrusive_pointer::{
    DynamicCastTagSharedIntrusive, IntrusiveDynamicCast, IntrusiveObject, IntrusiveStaticCast,
    SharedIntrusive, SharedWeakUnion, StaticCastTagSharedIntrusive, WeakIntrusive,
    dynamic_pointer_cast, make_shared_intrusive, static_pointer_cast,
};
use basics::intrusive_ref_counts::IntrusiveRefCounts;
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Barrier, Mutex};
use std::thread;
use std::time::Duration;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CastLifecycle {
    Alive = 1,
    PartiallyDeleted = 2,
    Deleted = 3,
}

impl CastLifecycle {
    fn load(state: &AtomicU8) -> Self {
        match state.load(Ordering::SeqCst) {
            1 => Self::Alive,
            2 => Self::PartiallyDeleted,
            3 => Self::Deleted,
            other => panic!("unexpected cast lifecycle state: {other}"),
        }
    }
}

#[derive(Debug)]
struct CastTracker {
    base: AtomicU8,
    derived: AtomicU8,
}

impl CastTracker {
    fn new() -> Self {
        Self {
            base: AtomicU8::new(CastLifecycle::Alive as u8),
            derived: AtomicU8::new(CastLifecycle::Alive as u8),
        }
    }
}

#[derive(Debug)]
struct PartialDeleteTracker {
    partial_started: AtomicU8,
    partial_finished: AtomicU8,
    deleted: AtomicU8,
    delete_saw_partial_finished: AtomicU8,
    barrier: Barrier,
    callback_sleep: Mutex<Duration>,
}

impl PartialDeleteTracker {
    fn new() -> Self {
        Self {
            partial_started: AtomicU8::new(0),
            partial_finished: AtomicU8::new(0),
            deleted: AtomicU8::new(0),
            delete_saw_partial_finished: AtomicU8::new(0),
            barrier: Barrier::new(2),
            callback_sleep: Mutex::new(Duration::from_millis(100)),
        }
    }
}

#[derive(Debug)]
struct PartialDeleteNode {
    ref_counts: IntrusiveRefCounts,
    tracker: Arc<PartialDeleteTracker>,
}

impl PartialDeleteNode {
    fn new(tracker: Arc<PartialDeleteTracker>) -> Self {
        Self {
            ref_counts: IntrusiveRefCounts::new(),
            tracker,
        }
    }
}

unsafe impl IntrusiveObject for PartialDeleteNode {
    type Owner = basics::intrusive_pointer::ErasedIntrusiveOwner;

    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
        &self.ref_counts
    }

    fn partial_destructor(&self) {
        self.tracker.partial_started.store(1, Ordering::SeqCst);
        self.tracker.barrier.wait();
        thread::sleep(
            *self
                .tracker
                .callback_sleep
                .lock()
                .expect("partial delete sleep mutex poisoned"),
        );
        self.tracker.partial_finished.store(1, Ordering::SeqCst);
    }
}

impl Drop for PartialDeleteNode {
    fn drop(&mut self) {
        self.tracker.delete_saw_partial_finished.store(
            self.tracker.partial_finished.load(Ordering::SeqCst),
            Ordering::SeqCst,
        );
        self.tracker.deleted.store(1, Ordering::SeqCst);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CastKind {
    Base,
    Derived,
}

#[derive(Debug)]
struct CastBase {
    ref_counts: IntrusiveRefCounts,
    tracker: Arc<CastTracker>,
    kind: CastKind,
}

impl CastBase {
    fn new(tracker: Arc<CastTracker>, kind: CastKind) -> Self {
        Self {
            ref_counts: IntrusiveRefCounts::new(),
            tracker,
            kind,
        }
    }
}

unsafe impl IntrusiveObject for CastBase {
    type Owner = basics::intrusive_pointer::ErasedIntrusiveOwner;

    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
        &self.ref_counts
    }

    fn partial_destructor(&self) {
        self.tracker
            .base
            .store(CastLifecycle::PartiallyDeleted as u8, Ordering::SeqCst);
    }
}

impl Drop for CastBase {
    fn drop(&mut self) {
        self.tracker
            .base
            .store(CastLifecycle::Deleted as u8, Ordering::SeqCst);
    }
}

#[repr(C)]
#[derive(Debug)]
struct CastDerived {
    base: CastBase,
    payload: u32,
}

impl CastDerived {
    fn new(tracker: Arc<CastTracker>) -> Self {
        Self {
            base: CastBase::new(tracker, CastKind::Derived),
            payload: 7,
        }
    }
}

unsafe impl IntrusiveObject for CastDerived {
    type Owner = basics::intrusive_pointer::ErasedIntrusiveOwner;

    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
        &self.base.ref_counts
    }

    fn partial_destructor(&self) {
        self.base
            .tracker
            .derived
            .store(CastLifecycle::PartiallyDeleted as u8, Ordering::SeqCst);
    }
}

impl Drop for CastDerived {
    fn drop(&mut self) {
        self.base
            .tracker
            .derived
            .store(CastLifecycle::Deleted as u8, Ordering::SeqCst);
    }
}

impl IntrusiveStaticCast<CastBase> for CastDerived {
    fn intrusive_static_cast(ptr: std::ptr::NonNull<Self>) -> std::ptr::NonNull<CastBase> {
        ptr.cast()
    }
}

impl IntrusiveDynamicCast<CastDerived> for CastBase {
    fn intrusive_dynamic_cast(
        ptr: std::ptr::NonNull<Self>,
    ) -> Option<std::ptr::NonNull<CastDerived>> {
        if unsafe { ptr.as_ref() }.kind == CastKind::Derived {
            Some(ptr.cast())
        } else {
            None
        }
    }
}

const STRESS_PARTIAL: u8 = 1;
const STRESS_DELETED: u8 = 2;
const STRESS_VIOLATION: u8 = 4;

#[derive(Debug, Default)]
struct StressOrderTracker {
    state: AtomicU8,
}

impl StressOrderTracker {
    fn new() -> Self {
        Self::default()
    }

    fn record_partial(&self) {
        if self.state.load(Ordering::SeqCst) & STRESS_DELETED != 0 {
            self.state.fetch_or(STRESS_VIOLATION, Ordering::SeqCst);
        }
        self.state.fetch_or(STRESS_PARTIAL, Ordering::SeqCst);
    }

    fn record_deleted(&self) {
        if self.state.load(Ordering::SeqCst) & STRESS_DELETED != 0 {
            self.state.fetch_or(STRESS_VIOLATION, Ordering::SeqCst);
        }
        self.state.fetch_or(STRESS_DELETED, Ordering::SeqCst);
    }

    fn partial_ran(&self) -> bool {
        self.state.load(Ordering::SeqCst) & STRESS_PARTIAL != 0
    }

    fn deleted_ran(&self) -> bool {
        self.state.load(Ordering::SeqCst) & STRESS_DELETED != 0
    }

    fn violated(&self) -> bool {
        self.state.load(Ordering::SeqCst) & STRESS_VIOLATION != 0
    }
}

#[derive(Debug)]
struct StressNode {
    ref_counts: IntrusiveRefCounts,
    tracker: Arc<StressOrderTracker>,
}

impl StressNode {
    fn new(tracker: Arc<StressOrderTracker>) -> Self {
        Self {
            ref_counts: IntrusiveRefCounts::new(),
            tracker,
        }
    }
}

unsafe impl IntrusiveObject for StressNode {
    type Owner = basics::intrusive_pointer::CompactIntrusiveOwner;

    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
        &self.ref_counts
    }

    fn partial_destructor(&self) {
        self.tracker.record_partial();
    }
}

impl Drop for StressNode {
    fn drop(&mut self) {
        self.tracker.record_deleted();
    }
}

#[derive(Clone)]
enum VariantEntry {
    Strong(SharedIntrusive<StressNode>),
    Weak(WeakIntrusive<StressNode>),
}

impl VariantEntry {
    fn touch(&self) {
        match self {
            Self::Strong(ptr) => {
                let _ = ptr.use_count();
            }
            Self::Weak(ptr) => {
                let _ = ptr.expired();
            }
        }
    }
}

#[test]
fn static_pointer_cast_preserves_owner_metadata() {
    let tracker = Arc::new(CastTracker::new());
    let derived = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));
    let casted = static_pointer_cast::<CastBase, _>(&derived);
    let weak = WeakIntrusive::from_shared(&casted);

    assert_eq!(derived.use_count(), 2);
    assert_eq!(casted.use_count(), 2);
    assert_eq!(
        casted.get().expect("base view should exist").kind,
        CastKind::Derived
    );

    drop(derived);
    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(CastLifecycle::load(&tracker.derived), CastLifecycle::Alive);

    drop(casted);
    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::PartiallyDeleted
    );
    assert!(weak.expired());
    assert!(weak.lock().is_null());

    drop(weak);
    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn static_pointer_cast_from_owned_preserves_reference_count() {
    let tracker = Arc::new(CastTracker::new());
    let derived = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));

    let casted: SharedIntrusive<CastBase> = derived.static_pointer_cast_owned();
    let weak = WeakIntrusive::from(&casted);

    assert_eq!(casted.use_count(), 1);
    assert_eq!(
        casted.get().expect("base view should exist").kind,
        CastKind::Derived
    );

    drop(casted);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::PartiallyDeleted
    );
    assert!(weak.expired());
    assert!(weak.lock().is_null());

    drop(weak);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn shared_intrusive_same_type_move_constructor_and_assignment_match_cpp_shape() {
    let tracker1 = Arc::new(CastTracker::new());
    let tracker2 = Arc::new(CastTracker::new());

    let original = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker1)));
    let original_weak: WeakIntrusive<CastDerived> = WeakIntrusive::from(&original);
    let moved = original;

    assert_eq!(moved.use_count(), 1);
    assert_eq!(
        moved
            .get()
            .expect("moved shared pointer should still expose payload")
            .payload,
        7
    );
    assert!(!original_weak.expired());

    let mut assigned = moved;
    assert_eq!(assigned.use_count(), 1);

    let replacement = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker2)));
    let replacement_weak: WeakIntrusive<CastDerived> = WeakIntrusive::from(&replacement);
    let moved_weak: WeakIntrusive<CastDerived> = WeakIntrusive::from(&assigned);
    assigned = replacement;

    assert!(moved_weak.expired());
    assert!(moved_weak.lock().is_null());
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::PartiallyDeleted
    );

    drop(moved_weak);
    drop(original_weak);
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::Deleted
    );

    assert_eq!(assigned.use_count(), 1);
    assert!(!replacement_weak.expired());
    assert_eq!(
        assigned
            .get()
            .expect("assigned shared pointer should now expose replacement payload")
            .payload,
        7
    );

    drop(assigned);
    assert!(replacement_weak.expired());
    drop(replacement_weak);
    assert_eq!(CastLifecycle::load(&tracker2.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker2.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn weak_intrusive_same_type_move_constructor_shape() {
    let tracker = Arc::new(CastTracker::new());
    let strong = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));
    let weak: WeakIntrusive<CastDerived> = WeakIntrusive::from(&strong);
    let moved = weak;

    assert!(!moved.expired());
    assert_eq!(
        moved
            .lock()
            .get()
            .expect("moved weak pointer should still lock payload")
            .payload,
        7
    );

    drop(strong);
    assert!(moved.expired());
    assert!(moved.lock().is_null());
    drop(moved);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn shared_weak_union_same_type_move_constructor_and_assignment_match_cpp_shape() {
    let tracker1 = Arc::new(CastTracker::new());
    let tracker2 = Arc::new(CastTracker::new());

    let first = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker1)));
    let first_weak: WeakIntrusive<CastBase> = WeakIntrusive::from(&first);
    let union = SharedWeakUnion::<CastBase>::from(first);
    let moved = union;

    assert!(moved.is_strong());
    assert_eq!(moved.use_count(), 1);
    assert_eq!(
        moved
            .get()
            .expect("moved union should still expose first owner")
            .kind,
        CastKind::Derived
    );

    let mut assigned = moved;
    assert!(assigned.is_strong());
    assert_eq!(assigned.use_count(), 1);

    let second = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker2)));
    let second_weak: WeakIntrusive<CastBase> = WeakIntrusive::from(&second);
    let moved_locked = assigned.lock();
    let moved_weak: WeakIntrusive<CastBase> = WeakIntrusive::from_shared(&moved_locked);
    drop(moved_locked);
    assigned = SharedWeakUnion::from(second);

    assert!(moved_weak.expired());
    assert!(moved_weak.lock().is_null());
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::PartiallyDeleted
    );

    drop(moved_weak);
    drop(first_weak);
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::Deleted
    );

    assert!(assigned.is_strong());
    assert_eq!(assigned.use_count(), 1);
    assert_eq!(
        assigned
            .get()
            .expect("assigned union should now expose replacement owner")
            .kind,
        CastKind::Derived
    );

    drop(assigned);
    assert!(second_weak.expired());
    drop(second_weak);
    assert_eq!(CastLifecycle::load(&tracker2.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker2.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn into_shared_intrusive_converting_move_constructor_and_assignment_shape() {
    let tracker = Arc::new(CastTracker::new());
    let derived = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));

    let casted: SharedIntrusive<CastBase> = derived.into_shared_intrusive();
    let weak = WeakIntrusive::from(&casted);

    assert_eq!(casted.use_count(), 1);
    assert_eq!(
        casted.get().expect("base view should exist").kind,
        CastKind::Derived
    );

    drop(casted);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::PartiallyDeleted
    );
    assert!(weak.expired());
    assert!(weak.lock().is_null());

    drop(weak);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );

    let previous_tracker = Arc::new(CastTracker::new());
    let previous = make_shared_intrusive(CastDerived::new(Arc::clone(&previous_tracker)));
    let previous_weak: WeakIntrusive<CastDerived> = WeakIntrusive::from_shared(&previous);
    let mut assigned: SharedIntrusive<CastBase> = previous.into_shared_intrusive();
    assert_eq!(assigned.use_count(), 1);
    assert_eq!(
        assigned
            .get()
            .expect("initial assigned base view should exist")
            .kind,
        CastKind::Derived
    );

    let next_tracker = Arc::new(CastTracker::new());
    let next = make_shared_intrusive(CastDerived::new(Arc::clone(&next_tracker)));
    assigned = next.into_shared_intrusive();

    assert!(previous_weak.expired());
    assert!(previous_weak.lock().is_null());
    assert_eq!(
        CastLifecycle::load(&previous_tracker.base),
        CastLifecycle::Alive
    );
    assert_eq!(
        CastLifecycle::load(&previous_tracker.derived),
        CastLifecycle::PartiallyDeleted
    );
    assert_eq!(
        assigned
            .get()
            .expect("replacement base view should exist")
            .kind,
        CastKind::Derived
    );
    assert_eq!(assigned.use_count(), 1);

    drop(previous_weak);
    assert_eq!(
        CastLifecycle::load(&previous_tracker.base),
        CastLifecycle::Deleted
    );
    assert_eq!(
        CastLifecycle::load(&previous_tracker.derived),
        CastLifecycle::Deleted
    );

    let next_weak = WeakIntrusive::from(&assigned);
    drop(assigned);
    assert!(next_weak.expired());
    drop(next_weak);
    assert_eq!(
        CastLifecycle::load(&next_tracker.base),
        CastLifecycle::Deleted
    );
    assert_eq!(
        CastLifecycle::load(&next_tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn shared_intrusive_related_type_assignment_assignment_shape() {
    let tracker1 = Arc::new(CastTracker::new());
    let tracker2 = Arc::new(CastTracker::new());

    let first = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker1)));
    let second = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker2)));
    let first_weak: WeakIntrusive<CastBase> = WeakIntrusive::from(&first);

    let mut assigned: SharedIntrusive<CastBase> = (&first).into();
    assert_eq!(first.use_count(), 2);
    assert_eq!(
        assigned
            .get()
            .expect("assigned pointer should initially expose first base view")
            .kind,
        CastKind::Derived
    );

    assigned.assign_from_shared(&second);
    assert_eq!(first.use_count(), 1);
    assert_eq!(second.use_count(), 2);
    assert_eq!(
        assigned
            .get()
            .expect("assigned pointer should now expose second base view")
            .kind,
        CastKind::Derived
    );

    drop(first);
    assert!(first_weak.expired());
    assert!(first_weak.lock().is_null());
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::PartiallyDeleted
    );

    drop(first_weak);
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::Deleted
    );

    drop(assigned);
    drop(second);
    assert_eq!(CastLifecycle::load(&tracker2.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker2.derived),
        CastLifecycle::Deleted
    );

    let tracker3 = Arc::new(CastTracker::new());
    let tracker4 = Arc::new(CastTracker::new());
    let third = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker3)));
    let third_weak: WeakIntrusive<CastBase> = WeakIntrusive::from(&third);
    let mut assigned_owned: SharedIntrusive<CastBase> = third.into_shared_intrusive();

    let fourth = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker4)));
    let fourth_weak: WeakIntrusive<CastBase> = WeakIntrusive::from(&fourth);
    assigned_owned.assign_from_shared_owned(fourth);

    assert!(third_weak.expired());
    assert!(third_weak.lock().is_null());
    assert_eq!(CastLifecycle::load(&tracker3.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker3.derived),
        CastLifecycle::PartiallyDeleted
    );

    drop(third_weak);
    assert_eq!(CastLifecycle::load(&tracker3.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker3.derived),
        CastLifecycle::Deleted
    );

    assert!(!fourth_weak.expired());
    assert_eq!(
        assigned_owned
            .get()
            .expect("owned reassignment should expose fourth base view")
            .kind,
        CastKind::Derived
    );

    drop(assigned_owned);
    assert!(fourth_weak.expired());
    assert!(fourth_weak.lock().is_null());
    assert_eq!(CastLifecycle::load(&tracker4.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker4.derived),
        CastLifecycle::PartiallyDeleted
    );

    drop(fourth_weak);
    assert_eq!(CastLifecycle::load(&tracker4.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker4.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn static_cast_tag_shared_intrusive_cast_constructor_shape() {
    let borrowed_tracker = Arc::new(CastTracker::new());
    let borrowed = make_shared_intrusive(CastDerived::new(Arc::clone(&borrowed_tracker)));

    let casted: SharedIntrusive<CastBase> =
        SharedIntrusive::from((StaticCastTagSharedIntrusive, &borrowed));
    assert_eq!(borrowed.use_count(), 2);
    assert_eq!(casted.use_count(), 2);
    assert_eq!(
        casted
            .get()
            .expect("borrowed cast-tag base view should exist")
            .kind,
        CastKind::Derived
    );

    drop(borrowed);
    assert_eq!(
        CastLifecycle::load(&borrowed_tracker.base),
        CastLifecycle::Alive
    );
    assert_eq!(
        CastLifecycle::load(&borrowed_tracker.derived),
        CastLifecycle::Alive
    );

    drop(casted);
    assert_eq!(
        CastLifecycle::load(&borrowed_tracker.base),
        CastLifecycle::Deleted
    );
    assert_eq!(
        CastLifecycle::load(&borrowed_tracker.derived),
        CastLifecycle::Deleted
    );

    let owned_tracker = Arc::new(CastTracker::new());
    let owned = make_shared_intrusive(CastDerived::new(Arc::clone(&owned_tracker)));

    let casted_owned: SharedIntrusive<CastBase> =
        SharedIntrusive::from((StaticCastTagSharedIntrusive, owned));
    let weak = WeakIntrusive::from(&casted_owned);

    assert_eq!(casted_owned.use_count(), 1);
    assert_eq!(
        casted_owned
            .get()
            .expect("owned cast-tag base view should exist")
            .kind,
        CastKind::Derived
    );

    drop(casted_owned);
    assert_eq!(
        CastLifecycle::load(&owned_tracker.base),
        CastLifecycle::Alive
    );
    assert_eq!(
        CastLifecycle::load(&owned_tracker.derived),
        CastLifecycle::PartiallyDeleted
    );
    assert!(weak.expired());

    drop(weak);
    assert_eq!(
        CastLifecycle::load(&owned_tracker.base),
        CastLifecycle::Deleted
    );
    assert_eq!(
        CastLifecycle::load(&owned_tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn dynamic_cast_tag_shared_intrusive_cast_constructor_shape() {
    let borrowed_tracker = Arc::new(CastTracker::new());
    let base_only =
        make_shared_intrusive(CastBase::new(Arc::clone(&borrowed_tracker), CastKind::Base));
    let borrowed_failed: SharedIntrusive<CastDerived> =
        SharedIntrusive::from((DynamicCastTagSharedIntrusive, &base_only));

    assert!(borrowed_failed.is_null());
    assert_eq!(base_only.use_count(), 1);

    let borrowed_derived = make_shared_intrusive(CastDerived::new(Arc::clone(&borrowed_tracker)));
    let borrowed_base = static_pointer_cast::<CastBase, _>(&borrowed_derived);
    let borrowed_round_trip: SharedIntrusive<CastDerived> =
        SharedIntrusive::from((DynamicCastTagSharedIntrusive, &borrowed_base));

    assert_eq!(borrowed_round_trip.use_count(), 3);
    assert_eq!(
        borrowed_round_trip
            .get()
            .expect("borrowed dynamic cast-tag derived view should exist")
            .payload,
        7
    );

    drop(borrowed_failed);
    drop(base_only);
    drop(borrowed_round_trip);
    drop(borrowed_base);
    drop(borrowed_derived);
    assert_eq!(
        CastLifecycle::load(&borrowed_tracker.base),
        CastLifecycle::Deleted
    );
    assert_eq!(
        CastLifecycle::load(&borrowed_tracker.derived),
        CastLifecycle::Deleted
    );

    let owned_tracker = Arc::new(CastTracker::new());
    let owned_derived = make_shared_intrusive(CastDerived::new(Arc::clone(&owned_tracker)));
    let owned_base = static_pointer_cast::<CastBase, _>(&owned_derived);
    let owned_round_trip =
        SharedIntrusive::<CastDerived>::try_from((DynamicCastTagSharedIntrusive, owned_base))
            .expect("owned dynamic cast-tag should succeed for derived runtime kind");
    let weak: WeakIntrusive<CastDerived> = WeakIntrusive::from(&owned_round_trip);

    assert_eq!(owned_derived.use_count(), 2);
    assert_eq!(owned_round_trip.use_count(), 2);
    assert_eq!(
        owned_round_trip
            .get()
            .expect("owned dynamic cast-tag derived view should exist")
            .payload,
        7
    );

    drop(owned_derived);
    drop(owned_round_trip);
    assert_eq!(
        CastLifecycle::load(&owned_tracker.base),
        CastLifecycle::Alive
    );
    assert_eq!(
        CastLifecycle::load(&owned_tracker.derived),
        CastLifecycle::PartiallyDeleted
    );
    assert!(weak.expired());

    drop(weak);
    assert_eq!(
        CastLifecycle::load(&owned_tracker.base),
        CastLifecycle::Deleted
    );
    assert_eq!(
        CastLifecycle::load(&owned_tracker.derived),
        CastLifecycle::Deleted
    );

    let failed_tracker = Arc::new(CastTracker::new());
    let failed_base =
        make_shared_intrusive(CastBase::new(Arc::clone(&failed_tracker), CastKind::Base));
    let failed_owned =
        SharedIntrusive::<CastDerived>::try_from((DynamicCastTagSharedIntrusive, failed_base));

    assert!(failed_owned.is_err());

    let restored = failed_owned.expect_err("failed move cast-tag should restore source owner");
    assert_eq!(restored.use_count(), 1);
    assert_eq!(
        restored
            .get()
            .expect("restored base pointer should exist after failed move cast-tag")
            .kind,
        CastKind::Base
    );

    drop(restored);
    assert_eq!(
        CastLifecycle::load(&failed_tracker.base),
        CastLifecycle::Deleted
    );
    assert_eq!(
        CastLifecycle::load(&failed_tracker.derived),
        CastLifecycle::Alive
    );
}

#[test]
fn partial_delete_waits_for_completion_before_final_delete() {
    let tracker = Arc::new(PartialDeleteTracker::new());
    let strong = make_shared_intrusive(PartialDeleteNode::new(Arc::clone(&tracker)));
    let weak = WeakIntrusive::from_shared(&strong);
    let weak_tracker = Arc::clone(&tracker);

    let weak_thread = thread::spawn(move || {
        weak_tracker.barrier.wait();
        let mut weak = weak;
        weak.reset();
    });

    let strong_thread = thread::spawn(move || {
        let mut strong = strong;
        strong.reset();
    });

    strong_thread.join().expect("join strong thread");
    weak_thread.join().expect("join weak thread");

    assert_eq!(tracker.partial_started.load(Ordering::SeqCst), 1);
    assert_eq!(tracker.partial_finished.load(Ordering::SeqCst), 1);
    assert_eq!(tracker.deleted.load(Ordering::SeqCst), 1);
    assert_eq!(
        tracker.delete_saw_partial_finished.load(Ordering::SeqCst),
        1
    );
}

#[test]
fn weak_reset_before_last_strong_reset_skips_partial_delete() {
    let tracker = Arc::new(PartialDeleteTracker::new());
    let strong = make_shared_intrusive(PartialDeleteNode::new(Arc::clone(&tracker)));
    let weak = WeakIntrusive::from_shared(&strong);
    let sync = Arc::new(Barrier::new(2));

    let weak_thread = {
        let sync = Arc::clone(&sync);
        thread::spawn(move || {
            let mut weak = weak;
            weak.reset();
            sync.wait();
        })
    };

    let strong_thread = {
        let sync = Arc::clone(&sync);
        thread::spawn(move || {
            sync.wait();
            let mut strong = strong;
            strong.reset();
        })
    };

    weak_thread.join().expect("join weak thread");
    strong_thread.join().expect("join strong thread");

    assert_eq!(tracker.partial_started.load(Ordering::SeqCst), 0);
    assert_eq!(tracker.partial_finished.load(Ordering::SeqCst), 0);
    assert_eq!(tracker.deleted.load(Ordering::SeqCst), 1);
    assert_eq!(
        tracker.delete_saw_partial_finished.load(Ordering::SeqCst),
        0
    );
}

#[test]
fn static_pointer_cast_from_borrowed_matches_const_ref_constructor_shape() {
    let tracker = Arc::new(CastTracker::new());
    let derived = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));

    let casted: SharedIntrusive<CastBase> = (&derived).into();
    assert_eq!(derived.use_count(), 2);
    assert_eq!(casted.use_count(), 2);
    assert_eq!(
        casted.get().expect("base view should exist").kind,
        CastKind::Derived
    );

    drop(derived);
    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(CastLifecycle::load(&tracker.derived), CastLifecycle::Alive);

    drop(casted);
    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn dynamic_pointer_cast_matches_runtime_kind() {
    let tracker = Arc::new(CastTracker::new());
    let base_only = make_shared_intrusive(CastBase::new(Arc::clone(&tracker), CastKind::Base));

    let failed = dynamic_pointer_cast::<CastDerived, _>(&base_only);
    assert!(failed.is_null());
    assert_eq!(base_only.use_count(), 1);
    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(CastLifecycle::load(&tracker.derived), CastLifecycle::Alive);

    let derived = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));
    let base_view = static_pointer_cast::<CastBase, _>(&derived);
    let round_trip = dynamic_pointer_cast::<CastDerived, _>(&base_view);

    assert!(!round_trip.is_null());
    assert_eq!(round_trip.use_count(), 3);
    assert_eq!(
        round_trip.get().expect("derived view should exist").payload,
        7
    );

    drop(round_trip);
    drop(base_view);
    drop(derived);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn borrowed_dynamic_cast_helper_constructor_shape() {
    let tracker = Arc::new(CastTracker::new());
    let base_only = make_shared_intrusive(CastBase::new(Arc::clone(&tracker), CastKind::Base));

    let failed = SharedIntrusive::<CastBase>::from_borrowed_dynamic_cast::<CastDerived>(&base_only);
    assert!(failed.is_null());
    assert_eq!(base_only.use_count(), 1);
    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(CastLifecycle::load(&tracker.derived), CastLifecycle::Alive);

    let derived = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));
    let base_view = static_pointer_cast::<CastBase, _>(&derived);
    let round_trip =
        SharedIntrusive::<CastBase>::from_borrowed_dynamic_cast::<CastDerived>(&base_view);

    assert!(!round_trip.is_null());
    assert_eq!(round_trip.use_count(), 3);
    assert_eq!(
        round_trip.get().expect("derived view should exist").payload,
        7
    );

    drop(round_trip);
    drop(base_view);
    drop(derived);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn owned_dynamic_pointer_cast_preserves_move_success_and_failure_shapes() {
    let tracker = Arc::new(CastTracker::new());
    let derived = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));
    let base_view = static_pointer_cast::<CastBase, _>(&derived);

    let round_trip = base_view
        .try_dynamic_pointer_cast_owned::<CastDerived>()
        .expect("owned dynamic cast should succeed for derived runtime kind");
    let weak: WeakIntrusive<CastDerived> = WeakIntrusive::from(&round_trip);

    assert_eq!(derived.use_count(), 2);
    assert_eq!(round_trip.use_count(), 2);
    assert_eq!(
        round_trip.get().expect("derived view should exist").payload,
        7
    );

    drop(derived);
    drop(round_trip);
    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::PartiallyDeleted
    );
    assert!(weak.expired());
    drop(weak);
    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );

    let base_tracker = Arc::new(CastTracker::new());
    let base_only = make_shared_intrusive(CastBase::new(Arc::clone(&base_tracker), CastKind::Base));
    let failed = base_only.try_dynamic_pointer_cast_owned::<CastDerived>();
    assert!(failed.is_err());

    let restored = failed.expect_err("base-only owned dynamic cast should restore source pointer");
    assert_eq!(restored.use_count(), 1);
    assert_eq!(
        restored
            .get()
            .expect("restored base pointer should exist")
            .kind,
        CastKind::Base
    );

    drop(restored);
    assert_eq!(
        CastLifecycle::load(&base_tracker.base),
        CastLifecycle::Deleted
    );
    assert_eq!(
        CastLifecycle::load(&base_tracker.derived),
        CastLifecycle::Alive
    );
}

#[test]
fn weak_intrusive_from_derived_shared_convertible_constructor_shape() {
    let tracker = Arc::new(CastTracker::new());
    let derived = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));
    let weak_base: WeakIntrusive<CastBase> = (&derived).into();

    assert_eq!(derived.use_count(), 1);
    assert!(!weak_base.expired());
    assert_eq!(
        weak_base
            .lock()
            .get()
            .expect("base view should lock while strong ref exists")
            .kind,
        CastKind::Derived
    );

    drop(derived);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::PartiallyDeleted
    );
    assert!(weak_base.expired());
    assert!(weak_base.lock().is_null());

    drop(weak_base);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn shared_weak_union_from_derived_shared_convertible_owner_shapes() {
    let tracker = Arc::new(CastTracker::new());
    let derived = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));
    let borrowed_union: SharedWeakUnion<CastBase> = (&derived).into();

    assert!(borrowed_union.is_strong());
    assert_eq!(derived.use_count(), 2);
    assert_eq!(
        borrowed_union
            .get()
            .expect("borrowed base view should exist")
            .kind,
        CastKind::Derived
    );

    drop(borrowed_union);
    assert_eq!(derived.use_count(), 1);

    let owned_union: SharedWeakUnion<CastBase> = derived.into();
    assert!(owned_union.is_strong());
    assert_eq!(owned_union.use_count(), 1);
    assert_eq!(
        owned_union
            .get()
            .expect("owned base view should exist")
            .kind,
        CastKind::Derived
    );

    let mut weak_union = owned_union.clone();
    assert!(weak_union.convert_to_weak());
    assert!(weak_union.is_weak());
    assert_eq!(owned_union.use_count(), 1);

    drop(owned_union);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::PartiallyDeleted
    );
    assert!(weak_union.expired());
    assert!(weak_union.lock().is_null());

    drop(weak_union);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn shared_weak_union_bool_operator_bool_shape() {
    let tracker = Arc::new(CastTracker::new());
    let strong = SharedWeakUnion::from(make_shared_intrusive(CastDerived::new(Arc::clone(
        &tracker,
    ))));

    assert!(bool::from(&strong));
    assert!(strong.get().is_some());

    let weak = strong.clone();
    assert!(bool::from(&weak));
    assert!(weak.get().is_some());

    let mut weak_representation = weak.clone();
    assert!(weak_representation.convert_to_weak());
    assert!(!bool::from(&weak_representation));
    assert!(weak_representation.get().is_none());

    let mut empty = SharedWeakUnion::<CastDerived>::new();
    assert!(!bool::from(&empty));
    assert!(empty.get().is_none());

    empty = weak_representation;
    assert!(!bool::from(&empty));
    assert!(empty.get().is_none());
}

#[test]
fn shared_weak_union_assignment_assignment_matrix() {
    let tracker1 = Arc::new(CastTracker::new());
    let tracker2 = Arc::new(CastTracker::new());

    let strong1 = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker1)));
    let strong2 = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker2)));

    let mut union1: SharedWeakUnion<CastBase> = (&strong1).into();
    let union2: SharedWeakUnion<CastBase> = (&strong2).into();

    assert!(union1.is_strong());
    assert!(union2.is_strong());
    assert_eq!(
        union1
            .get()
            .expect("first union should expose first object")
            .kind,
        CastKind::Derived
    );
    assert_eq!(
        union2
            .get()
            .expect("second union should expose second object")
            .kind,
        CastKind::Derived
    );
    assert_eq!(strong1.use_count(), 2);
    assert_eq!(strong2.use_count(), 2);

    union1 = union2.clone();
    assert!(union1.is_strong());
    assert_eq!(
        union1
            .get()
            .expect("assigned union should now expose second object") as *const CastBase,
        union2
            .get()
            .expect("source union should still expose second object") as *const CastBase
    );
    assert_eq!(strong1.use_count(), 1);
    assert_eq!(strong2.use_count(), 3);
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Alive);
    assert_eq!(CastLifecycle::load(&tracker2.base), CastLifecycle::Alive);

    let initial_refcount = strong2.use_count();
    union1 = union1.clone();
    assert!(union1.is_strong());
    assert_eq!(strong2.use_count(), initial_refcount);

    union1 = SharedWeakUnion::new();
    assert!(union1.get().is_none());
    assert_eq!(strong2.use_count(), 2);

    let mut weak_only: SharedWeakUnion<CastBase> = (&strong2).into();
    assert!(weak_only.convert_to_weak());
    assert!(weak_only.is_weak());
    drop(union2);
    drop(strong2);
    assert!(weak_only.expired());
    assert!(weak_only.lock().is_null());

    union1 = weak_only.clone();
    assert!(union1.is_weak());
    assert!(union1.get().is_none());
    assert!(union1.expired());
    assert!(union1.lock().is_null());

    drop(weak_only);
    drop(union1);

    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Alive);
    assert_eq!(CastLifecycle::load(&tracker1.derived), CastLifecycle::Alive);
    assert_eq!(CastLifecycle::load(&tracker2.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker2.derived),
        CastLifecycle::Deleted
    );

    drop(strong1);
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn weak_intrusive_replacement_from_strong_assignment_shape() {
    let tracker1 = Arc::new(CastTracker::new());
    let tracker2 = Arc::new(CastTracker::new());

    let strong1 = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker1)));
    let strong2 = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker2)));

    let mut weak: WeakIntrusive<CastBase> = WeakIntrusive::from(&strong1);
    assert!(!weak.expired());
    assert_eq!(
        weak.lock()
            .get()
            .expect("weak pointer should lock first strong owner")
            .kind,
        CastKind::Derived
    );

    weak.assign_from_shared(&strong2);
    drop(strong1);

    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::Deleted
    );

    assert!(!weak.expired());
    let locked = weak.lock();
    assert_eq!(
        locked
            .get()
            .expect("replaced weak pointer should lock second strong owner")
            .kind,
        CastKind::Derived
    );
    drop(locked);

    drop(strong2);
    assert!(weak.expired());
    assert!(weak.lock().is_null());

    drop(weak);
    assert_eq!(CastLifecycle::load(&tracker2.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker2.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn weak_intrusive_lock_is_stable_under_multithreaded_contention() {
    let tracker = Arc::new(CastTracker::new());
    let strong = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));
    let workers = 8;
    let iterations = 128;
    let barrier = Arc::new(Barrier::new(workers));

    let joins: Vec<_> = (0..workers)
        .map(|_| {
            let strong = strong.clone();
            let barrier = Arc::clone(&barrier);
            thread::spawn(move || {
                let weak: WeakIntrusive<CastDerived> = WeakIntrusive::from(&strong);
                barrier.wait();
                for _ in 0..iterations {
                    assert!(!weak.expired());
                    let locked = weak.lock();
                    assert!(!locked.is_null());
                    assert_eq!(
                        locked
                            .get()
                            .expect("locked strong pointer should stay valid")
                            .payload,
                        7
                    );
                }
            })
        })
        .collect();

    for join in joins {
        join.join().expect("weak locking worker should finish");
    }

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(CastLifecycle::load(&tracker.derived), CastLifecycle::Alive);

    drop(strong);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn shared_weak_union_flip_is_stable_under_multithreaded_contention() {
    let tracker = Arc::new(CastTracker::new());
    let strong = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker)));
    let workers = 8;
    let entries_per_worker = 16;
    let iterations = 64;
    let barrier = Arc::new(Barrier::new(workers));

    let joins: Vec<_> = (0..workers)
        .map(|worker| {
            let strong = strong.clone();
            let barrier = Arc::clone(&barrier);
            thread::spawn(move || {
                let mut entries: Vec<SharedWeakUnion<CastDerived>> = (0..entries_per_worker)
                    .map(|_| SharedWeakUnion::from(strong.clone()))
                    .collect();
                drop(strong);

                barrier.wait();

                for iteration in 0..iterations {
                    for (index, entry) in entries.iter_mut().enumerate() {
                        if (worker + iteration + index) % 2 == 0 {
                            assert!(entry.convert_to_weak());
                            assert!(entry.is_weak());
                            assert!(entry.get().is_none());
                        } else {
                            assert!(entry.convert_to_strong());
                            assert!(entry.is_strong());
                            assert_eq!(
                                entry
                                    .get()
                                    .expect("strong union entry should expose payload")
                                    .payload,
                                7
                            );
                        }
                    }
                }

                entries.clear();
            })
        })
        .collect();

    for join in joins {
        join.join().expect("shared weak union worker should finish");
    }

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Alive);
    assert_eq!(CastLifecycle::load(&tracker.derived), CastLifecycle::Alive);

    drop(strong);

    assert_eq!(CastLifecycle::load(&tracker.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn mixed_variant_clear_is_stable_under_multithreaded_contention() {
    let workers = 8;
    let loop_iters = 64;
    let entries_per_worker = 24;
    let start_barrier = Arc::new(Barrier::new(workers));
    let ready_barrier = Arc::new(Barrier::new(workers));
    let clear_barrier = Arc::new(Barrier::new(workers));
    let slots: Arc<Vec<Mutex<Option<SharedIntrusive<StressNode>>>>> =
        Arc::new((0..workers).map(|_| Mutex::new(None)).collect());
    let trackers: Arc<Vec<Mutex<Option<Arc<StressOrderTracker>>>>> =
        Arc::new((0..loop_iters).map(|_| Mutex::new(None)).collect());

    let joins: Vec<_> = (0..workers)
        .map(|worker| {
            let start_barrier = Arc::clone(&start_barrier);
            let ready_barrier = Arc::clone(&ready_barrier);
            let clear_barrier = Arc::clone(&clear_barrier);
            let slots = Arc::clone(&slots);
            let trackers = Arc::clone(&trackers);
            thread::spawn(move || {
                for iter in 0..loop_iters {
                    start_barrier.wait();

                    if worker == 0 {
                        if iter > 0 {
                            let previous = trackers[iter - 1]
                                .lock()
                                .expect("previous tracker mutex poisoned")
                                .clone()
                                .expect("previous tracker should exist");
                            assert!(previous.deleted_ran());
                            assert!(!previous.violated());
                        }

                        let tracker = Arc::new(StressOrderTracker::new());
                        *trackers[iter].lock().expect("tracker mutex poisoned") =
                            Some(Arc::clone(&tracker));

                        let strong = make_shared_intrusive(StressNode::new(tracker));
                        for slot in slots.iter() {
                            *slot.lock().expect("slot mutex poisoned") = Some(strong.clone());
                        }
                    }

                    ready_barrier.wait();

                    let to_clone = {
                        let mut slot = slots[worker].lock().expect("slot mutex poisoned");
                        slot.take().expect("worker clone source should exist")
                    };

                    let mut entries = Vec::with_capacity(entries_per_worker);
                    for index in 0..entries_per_worker {
                        if (worker + iter + index) % 2 == 0 {
                            entries.push(VariantEntry::Strong(to_clone.clone()));
                        } else {
                            entries.push(VariantEntry::Weak(WeakIntrusive::from(&to_clone)));
                        }
                    }
                    drop(to_clone);

                    clear_barrier.wait();
                    for entry in &entries {
                        entry.touch();
                    }
                    entries.clear();
                }
            })
        })
        .collect();

    for join in joins {
        join.join().expect("mixed variant worker should finish");
    }

    let last = trackers[loop_iters - 1]
        .lock()
        .expect("last tracker mutex poisoned")
        .clone()
        .expect("last tracker should exist");
    assert!(last.deleted_ran());
    assert!(!last.violated());
}

#[test]
fn mixed_union_clear_is_stable_under_multithreaded_contention() {
    let workers = 8;
    let loop_iters = 48;
    let entries_per_worker = 24;
    let flip_iters = 64;
    let start_barrier = Arc::new(Barrier::new(workers));
    let ready_barrier = Arc::new(Barrier::new(workers));
    let built_barrier = Arc::new(Barrier::new(workers));
    let clear_barrier = Arc::new(Barrier::new(workers));
    let slots: Arc<Vec<Mutex<Option<SharedIntrusive<StressNode>>>>> =
        Arc::new((0..workers).map(|_| Mutex::new(None)).collect());
    let trackers: Arc<Vec<Mutex<Option<Arc<StressOrderTracker>>>>> =
        Arc::new((0..loop_iters).map(|_| Mutex::new(None)).collect());

    let joins: Vec<_> = (0..workers)
        .map(|worker| {
            let start_barrier = Arc::clone(&start_barrier);
            let ready_barrier = Arc::clone(&ready_barrier);
            let built_barrier = Arc::clone(&built_barrier);
            let clear_barrier = Arc::clone(&clear_barrier);
            let slots = Arc::clone(&slots);
            let trackers = Arc::clone(&trackers);
            thread::spawn(move || {
                for iter in 0..loop_iters {
                    start_barrier.wait();

                    if worker == 0 {
                        if iter > 0 {
                            let previous = trackers[iter - 1]
                                .lock()
                                .expect("previous tracker mutex poisoned")
                                .clone()
                                .expect("previous tracker should exist");
                            assert!(previous.deleted_ran());
                            assert!(!previous.violated());
                        }

                        let tracker = Arc::new(StressOrderTracker::new());
                        *trackers[iter].lock().expect("tracker mutex poisoned") =
                            Some(Arc::clone(&tracker));

                        let strong = make_shared_intrusive(StressNode::new(tracker));
                        for slot in slots.iter() {
                            *slot.lock().expect("slot mutex poisoned") = Some(strong.clone());
                        }
                    }

                    ready_barrier.wait();

                    let to_clone = {
                        let mut slot = slots[worker].lock().expect("slot mutex poisoned");
                        slot.take().expect("worker clone source should exist")
                    };

                    let mut entries: Vec<SharedWeakUnion<StressNode>> = (0..entries_per_worker)
                        .map(|_| SharedWeakUnion::from(to_clone.clone()))
                        .collect();
                    drop(to_clone);

                    built_barrier.wait();

                    for flip in 0..flip_iters {
                        for (index, entry) in entries.iter_mut().enumerate() {
                            if (worker + iter + flip + index) % 2 == 0 {
                                assert!(entry.convert_to_weak());
                            } else {
                                assert!(entry.convert_to_strong());
                            }
                        }
                    }

                    clear_barrier.wait();
                    entries.clear();
                }
            })
        })
        .collect();

    for join in joins {
        join.join().expect("mixed union worker should finish");
    }

    let last = trackers[loop_iters - 1]
        .lock()
        .expect("last tracker mutex poisoned")
        .clone()
        .expect("last tracker should exist");
    assert!(last.deleted_ran());
    assert!(!last.violated());
    assert!(last.partial_ran() || last.deleted_ran());
}

#[test]
fn shared_weak_union_replacement_from_borrowed_strong_assignment_shape() {
    let tracker1 = Arc::new(CastTracker::new());
    let tracker2 = Arc::new(CastTracker::new());

    let strong1 = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker1)));
    let strong2 = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker2)));
    let weak1: WeakIntrusive<CastBase> = WeakIntrusive::from(&strong1);

    let mut union: SharedWeakUnion<CastBase> = (&strong1).into();
    assert_eq!(strong1.use_count(), 2);
    assert_eq!(
        union
            .get()
            .expect("union should initially expose first borrowed strong owner")
            .kind,
        CastKind::Derived
    );

    union.assign_from_shared(&strong2);
    assert_eq!(strong1.use_count(), 1);
    assert_eq!(strong2.use_count(), 2);
    assert_eq!(
        union
            .get()
            .expect("union should now expose second borrowed strong owner")
            .kind,
        CastKind::Derived
    );

    drop(strong1);
    assert!(weak1.expired());
    assert!(weak1.lock().is_null());
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::PartiallyDeleted
    );

    drop(weak1);
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::Deleted
    );

    drop(union);
    drop(strong2);
    assert_eq!(CastLifecycle::load(&tracker2.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker2.derived),
        CastLifecycle::Deleted
    );
}

#[test]
fn shared_weak_union_replacement_from_owned_strong_move_assignment_shape() {
    let tracker1 = Arc::new(CastTracker::new());
    let tracker2 = Arc::new(CastTracker::new());

    let first = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker1)));
    let first_weak: WeakIntrusive<CastBase> = WeakIntrusive::from(&first);
    let mut union: SharedWeakUnion<CastBase> = first.into();
    assert_eq!(
        union
            .get()
            .expect("union should initially expose first owned strong owner")
            .kind,
        CastKind::Derived
    );

    let second = make_shared_intrusive(CastDerived::new(Arc::clone(&tracker2)));
    let second_weak: WeakIntrusive<CastBase> = WeakIntrusive::from(&second);
    union.assign_from_shared_owned(second);

    assert!(first_weak.expired());
    assert!(first_weak.lock().is_null());
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::PartiallyDeleted
    );

    drop(first_weak);
    assert_eq!(CastLifecycle::load(&tracker1.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker1.derived),
        CastLifecycle::Deleted
    );

    assert!(!second_weak.expired());
    assert_eq!(
        union
            .get()
            .expect("union should now expose owned second strong owner")
            .kind,
        CastKind::Derived
    );

    drop(union);
    assert!(second_weak.expired());
    assert!(second_weak.lock().is_null());
    assert_eq!(CastLifecycle::load(&tracker2.base), CastLifecycle::Alive);
    assert_eq!(
        CastLifecycle::load(&tracker2.derived),
        CastLifecycle::PartiallyDeleted
    );
    drop(second_weak);

    assert_eq!(CastLifecycle::load(&tracker2.base), CastLifecycle::Deleted);
    assert_eq!(
        CastLifecycle::load(&tracker2.derived),
        CastLifecycle::Deleted
    );
}
