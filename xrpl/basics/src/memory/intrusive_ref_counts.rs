//! Rust port of `xrpl/basics/IntrusiveRefCounts.h`.
//!
//! This keeps the same packed-count model as the reference implementation:
//! - strong count in the low bits,
//! - weak count in the high count bits,
//! - one bit for "partial destroy started",
//! - one bit for "partial destroy finished".

use std::collections::HashMap;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Mutex, OnceLock};
use std::thread;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReleaseStrongRefAction {
    Noop,
    PartialDestroy,
    Destroy,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReleaseWeakRefAction {
    Noop,
    Destroy,
}

#[derive(Clone, Copy)]
enum OwnerDispatchAction {
    FinalDestroy,
    PartialDestroy,
}

type OwnerDispatch = unsafe fn(*mut (), OwnerDispatchAction);

#[derive(Clone, Copy)]
struct OwnerMetadata {
    ptr: usize,
    dispatch: usize,
}

// The intrusive control word must remain four bytes to match the reference
// node layouts. Allocation-specific destruction metadata therefore lives in a
// process-wide registry keyed by the address of that control word. The entry
// exists from first adoption through the final weak release, which is exactly
// the lifetime over which dispatch is needed.
fn owner_registry() -> &'static Mutex<HashMap<usize, OwnerMetadata>> {
    static REGISTRY: OnceLock<Mutex<HashMap<usize, OwnerMetadata>>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(HashMap::new()))
}

unsafe fn dispatch_owner<T: crate::intrusive_pointer::IntrusiveObject>(
    ptr: *mut (),
    action: OwnerDispatchAction,
) {
    match action {
        OwnerDispatchAction::FinalDestroy => unsafe { drop(Box::from_raw(ptr.cast::<T>())) },
        OwnerDispatchAction::PartialDestroy => unsafe { (&*ptr.cast::<T>()).partial_destructor() },
    }
}
#[derive(Debug)]
pub struct IntrusiveRefCounts {
    ref_counts: AtomicU32,
}

/// Marks partial destruction complete even when the user callback unwinds.
/// The final weak release waits for this marker before it can destroy the
/// allocation shell, so this guard must outlive the callback invocation.
struct PartialDestroyCompletion<'a>(&'a IntrusiveRefCounts);

impl Drop for PartialDestroyCompletion<'_> {
    fn drop(&mut self) {
        self.0.partial_destructor_finished();
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RefCountPair {
    strong: u16,
    weak: u16,
    partial_destroy_started_bit: u32,
    partial_destroy_finished_bit: u32,
}

const _: () = assert!(std::mem::size_of::<IntrusiveRefCounts>() == 4);
const _: () = assert!(std::mem::align_of::<IntrusiveRefCounts>() == 4);

impl Default for IntrusiveRefCounts {
    fn default() -> Self {
        Self::new()
    }
}

impl IntrusiveRefCounts {
    const ONE: u32 = 1;
    const STRONG_COUNT_BITS: u32 = u16::BITS;
    const WEAK_COUNT_BITS: u32 = Self::STRONG_COUNT_BITS - 2;
    const FIELD_TYPE_BITS: u32 = u32::BITS;

    const STRONG_DELTA: u32 = 1;
    const WEAK_DELTA: u32 = Self::ONE << Self::STRONG_COUNT_BITS;

    const PARTIAL_DESTROY_STARTED_MASK: u32 = Self::ONE << (Self::FIELD_TYPE_BITS - 1);
    const PARTIAL_DESTROY_FINISHED_MASK: u32 = Self::ONE << (Self::FIELD_TYPE_BITS - 2);

    const TAG_MASK: u32 = Self::PARTIAL_DESTROY_STARTED_MASK | Self::PARTIAL_DESTROY_FINISHED_MASK;
    const VALUE_MASK: u32 = !Self::TAG_MASK;
    const STRONG_MASK: u32 = ((Self::ONE << Self::STRONG_COUNT_BITS) - 1) & Self::VALUE_MASK;
    const WEAK_MASK: u32 =
        (((Self::ONE << Self::WEAK_COUNT_BITS) - 1) << Self::STRONG_COUNT_BITS) & Self::VALUE_MASK;

    pub const fn new() -> Self {
        Self {
            ref_counts: AtomicU32::new(Self::STRONG_DELTA),
        }
    }

    /// Registers the original concrete allocation exactly once. Views produced
    /// by intrusive casts share this control word, so the final destroy always
    /// uses the allocation's original type rather than a cast view.
    pub fn initialize_owner_metadata<T: crate::intrusive_pointer::IntrusiveObject>(
        &self,
        ptr: NonNull<T>,
    ) {
        let key = self as *const Self as usize;
        let metadata = OwnerMetadata {
            ptr: ptr.cast::<()>().as_ptr() as usize,
            dispatch: dispatch_owner::<T> as usize,
        };
        // Invalid raw-adoption tests intentionally panic. Drop the process-wide
        // lock before validating an existing record so those expected panics
        // cannot poison unrelated intrusive lifetimes.
        let existing = {
            let mut registry = owner_registry()
                .lock()
                .unwrap_or_else(|poison| poison.into_inner());
            match registry.entry(key) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(metadata);
                    None
                }
                std::collections::hash_map::Entry::Occupied(entry) => Some(*entry.get()),
            }
        };
        if let Some(existing) = existing {
            assert_eq!(
                existing.ptr, metadata.ptr,
                "intrusive owner metadata was initialized for another allocation"
            );
            assert_eq!(
                existing.dispatch, metadata.dispatch,
                "intrusive owner metadata was initialized for another type"
            );
        }
    }

    pub fn dispatch_partial_destroy(&self) {
        self.dispatch_partial_destroy_with(|| {
            let metadata = self.owner_metadata();
            let dispatch: OwnerDispatch = unsafe { std::mem::transmute(metadata.dispatch) };
            unsafe { dispatch(metadata.ptr as *mut (), OwnerDispatchAction::PartialDestroy) };
        });
    }

    /// Runs an object-specific partial destructor while guaranteeing that the
    /// retained allocation shell becomes eligible for final weak release even
    /// if the callback unwinds.
    pub fn dispatch_partial_destroy_with(&self, callback: impl FnOnce()) {
        let _completion = PartialDestroyCompletion(self);
        callback();
    }

    pub fn dispatch_final_destroy(&self) {
        let key = self as *const Self as usize;
        let metadata = owner_registry()
            .lock()
            .unwrap_or_else(|poison| poison.into_inner())
            .remove(&key)
            .expect("intrusive owner metadata was not initialized");
        let dispatch: OwnerDispatch = unsafe { std::mem::transmute(metadata.dispatch) };
        unsafe { dispatch(metadata.ptr as *mut (), OwnerDispatchAction::FinalDestroy) };
    }

    /// Returns whether this control word uses the generic out-of-object owner
    /// metadata path. Compact polymorphic objects may provide their own
    /// concrete destruction dispatch and deliberately return false.
    pub fn has_registered_owner_metadata(&self) -> bool {
        owner_registry()
            .lock()
            .unwrap_or_else(|poison| poison.into_inner())
            .contains_key(&(self as *const Self as usize))
    }

    fn owner_metadata(&self) -> OwnerMetadata {
        let key = self as *const Self as usize;
        *owner_registry()
            .lock()
            .unwrap_or_else(|poison| poison.into_inner())
            .get(&key)
            .expect("intrusive owner metadata was not initialized")
    }

    pub fn add_strong_ref(&self) {
        // Relaxed is sufficient for increment — matches reference shared_ptr.
        // Only the decrement (release_strong_ref) needs AcqRel to ensure
        // all writes are visible before the destructor runs.
        self.ref_counts
            .fetch_add(Self::STRONG_DELTA, Ordering::Relaxed);
    }

    pub fn add_weak_ref(&self) {
        self.ref_counts
            .fetch_add(Self::WEAK_DELTA, Ordering::Relaxed);
    }

    pub fn release_strong_ref(&self) -> ReleaseStrongRefAction {
        let mut previous = self.ref_counts.load(Ordering::Acquire);

        loop {
            let previous_pair = RefCountPair::from_raw(previous);
            debug_assert!(previous_pair.strong >= Self::STRONG_DELTA as u16);

            let mut next = previous - Self::STRONG_DELTA;
            let mut action = ReleaseStrongRefAction::Noop;

            if previous_pair.strong == 1 {
                if previous_pair.weak == 0 {
                    action = ReleaseStrongRefAction::Destroy;
                } else {
                    next |= Self::PARTIAL_DESTROY_STARTED_MASK;
                    action = ReleaseStrongRefAction::PartialDestroy;
                }
            }

            match self.ref_counts.compare_exchange_weak(
                previous,
                next,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    debug_assert!(
                        action == ReleaseStrongRefAction::Noop
                            || (previous & Self::PARTIAL_DESTROY_STARTED_MASK) == 0
                    );
                    return action;
                }
                Err(observed) => previous = observed,
            }
        }
    }

    pub fn add_weak_release_strong_ref(&self) -> ReleaseStrongRefAction {
        let delta = Self::WEAK_DELTA - Self::STRONG_DELTA;
        let mut previous = self.ref_counts.load(Ordering::Acquire);

        loop {
            let previous_pair = RefCountPair::from_raw(previous);
            debug_assert_eq!(previous_pair.partial_destroy_started_bit, 0);

            let mut next = previous + delta;
            let mut action = ReleaseStrongRefAction::Noop;

            if previous_pair.strong == 1 && previous_pair.weak != 0 {
                next |= Self::PARTIAL_DESTROY_STARTED_MASK;
                action = ReleaseStrongRefAction::PartialDestroy;
            }

            match self.ref_counts.compare_exchange_weak(
                previous,
                next,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    debug_assert!((previous & Self::PARTIAL_DESTROY_STARTED_MASK) == 0);
                    return action;
                }
                Err(observed) => previous = observed,
            }
        }
    }

    pub fn release_weak_ref(&self) -> ReleaseWeakRefAction {
        let mut previous = self
            .ref_counts
            .fetch_sub(Self::WEAK_DELTA, Ordering::AcqRel);
        let mut previous_pair = RefCountPair::from_raw(previous);

        if previous_pair.weak == 1 && previous_pair.strong == 0 {
            if previous_pair.partial_destroy_started_bit == 0
                && previous_pair.partial_destroy_finished_bit == 0
            {
                return ReleaseWeakRefAction::Destroy;
            }

            if previous_pair.partial_destroy_started_bit == 0 {
                previous = self.wait_until(|pair| pair.partial_destroy_started_bit != 0);
                previous_pair = RefCountPair::from_raw(previous);
            }

            if previous_pair.partial_destroy_finished_bit == 0 {
                self.wait_until(|pair| pair.partial_destroy_finished_bit != 0);
            }

            return ReleaseWeakRefAction::Destroy;
        }

        ReleaseWeakRefAction::Noop
    }

    pub fn checkout_strong_ref_from_weak(&self) -> bool {
        let mut current = RefCountPair::new(1, 1).combined_value();
        let mut desired = RefCountPair::new(2, 1).combined_value();

        loop {
            match self.ref_counts.compare_exchange_weak(
                current,
                desired,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => return true,
                Err(observed) => {
                    let previous = RefCountPair::from_raw(observed);
                    if previous.strong == 0 {
                        return false;
                    }

                    current = observed;
                    desired = current + Self::STRONG_DELTA;
                }
            }
        }
    }

    pub fn expired(&self) -> bool {
        RefCountPair::from_raw(self.ref_counts.load(Ordering::Acquire)).strong == 0
    }

    pub fn use_count(&self) -> usize {
        RefCountPair::from_raw(self.ref_counts.load(Ordering::Acquire)).strong as usize
    }

    pub fn partial_destroy_started(&self) -> bool {
        (self.ref_counts.load(Ordering::Acquire) & Self::PARTIAL_DESTROY_STARTED_MASK) != 0
    }

    pub fn partial_destructor_finished(&self) {
        let previous = self
            .ref_counts
            .fetch_or(Self::PARTIAL_DESTROY_FINISHED_MASK, Ordering::AcqRel);
        let previous_pair = RefCountPair::from_raw(previous);

        debug_assert!(
            previous_pair.partial_destroy_finished_bit == 0
                && previous_pair.partial_destroy_started_bit != 0
                && previous_pair.strong == 0
        );
    }

    fn wait_until(&self, mut predicate: impl FnMut(RefCountPair) -> bool) -> u32 {
        let mut spins = 0usize;

        loop {
            let value = self.ref_counts.load(Ordering::Acquire);
            if predicate(RefCountPair::from_raw(value)) {
                return value;
            }

            if spins < 64 {
                spins += 1;
                std::hint::spin_loop();
            } else {
                thread::yield_now();
            }
        }
    }
}

impl Drop for IntrusiveRefCounts {
    fn drop(&mut self) {
        if cfg!(debug_assertions) {
            let value = self.ref_counts.load(Ordering::Acquire);
            debug_assert_eq!(value & Self::VALUE_MASK, 0);

            let tags = value & Self::TAG_MASK;
            debug_assert!(tags == 0 || tags == Self::TAG_MASK);
        }
    }
}

impl RefCountPair {
    const CHECK_STRONG_MAX_VALUE: u16 = u16::MAX - 32;
    const CHECK_WEAK_MAX_VALUE: u16 = ((1u16 << IntrusiveRefCounts::WEAK_COUNT_BITS) - 1) - 32;

    fn from_raw(value: u32) -> Self {
        let strong = (value & IntrusiveRefCounts::STRONG_MASK) as u16;
        let weak = ((value & IntrusiveRefCounts::WEAK_MASK)
            >> IntrusiveRefCounts::STRONG_COUNT_BITS) as u16;

        debug_assert!(strong < Self::CHECK_STRONG_MAX_VALUE);
        debug_assert!(weak < Self::CHECK_WEAK_MAX_VALUE);

        Self {
            strong,
            weak,
            partial_destroy_started_bit: value & IntrusiveRefCounts::PARTIAL_DESTROY_STARTED_MASK,
            partial_destroy_finished_bit: value & IntrusiveRefCounts::PARTIAL_DESTROY_FINISHED_MASK,
        }
    }

    fn new(strong: u16, weak: u16) -> Self {
        debug_assert!(strong < Self::CHECK_STRONG_MAX_VALUE);
        debug_assert!(weak < Self::CHECK_WEAK_MAX_VALUE);

        Self {
            strong,
            weak,
            partial_destroy_started_bit: 0,
            partial_destroy_finished_bit: 0,
        }
    }

    fn combined_value(self) -> u32 {
        debug_assert!(self.strong < Self::CHECK_STRONG_MAX_VALUE);
        debug_assert!(self.weak < Self::CHECK_WEAK_MAX_VALUE);

        ((self.weak as u32) << IntrusiveRefCounts::STRONG_COUNT_BITS)
            | (self.strong as u32)
            | self.partial_destroy_started_bit
            | self.partial_destroy_finished_bit
    }
}

#[cfg(test)]
mod tests {
    use super::{IntrusiveRefCounts, ReleaseStrongRefAction, ReleaseWeakRefAction};

    #[test]
    fn direct_release_actions_match_cpp_roles() {
        let counts = IntrusiveRefCounts::new();
        assert_eq!(counts.use_count(), 1);

        counts.add_weak_ref();
        assert_eq!(
            counts.release_strong_ref(),
            ReleaseStrongRefAction::PartialDestroy
        );
        assert!(counts.expired());
        counts.partial_destructor_finished();
        assert_eq!(counts.release_weak_ref(), ReleaseWeakRefAction::Destroy);
    }

    #[test]
    fn convert_last_strong_to_weak_keeps_object_alive_for_weak_handles() {
        let counts = IntrusiveRefCounts::new();

        assert_eq!(
            counts.add_weak_release_strong_ref(),
            ReleaseStrongRefAction::Noop
        );
        assert!(counts.expired());
        assert_eq!(counts.use_count(), 0);
        assert_eq!(counts.release_weak_ref(), ReleaseWeakRefAction::Destroy);
    }

    #[test]
    fn weak_checkout_fails_after_strong_count_reaches_zero() {
        let counts = IntrusiveRefCounts::new();
        counts.add_weak_ref();

        assert!(counts.checkout_strong_ref_from_weak());
        assert_eq!(counts.use_count(), 2);

        assert_eq!(counts.release_strong_ref(), ReleaseStrongRefAction::Noop);
        assert_eq!(
            counts.release_strong_ref(),
            ReleaseStrongRefAction::PartialDestroy
        );
        assert!(!counts.checkout_strong_ref_from_weak());

        counts.partial_destructor_finished();
        assert_eq!(counts.release_weak_ref(), ReleaseWeakRefAction::Destroy);
    }
}
