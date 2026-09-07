//! Intrusive-pointer ownership types for the shared and weak parts of
//! `xrpl/basics/IntrusivePointer.h`.
//!
//! This module covers the intrusive-pointer ownership surface used by the
//! landed cache callers:
//! - `SharedIntrusive<T>`
//! - `WeakIntrusive<T>`
//! - `SharedWeakUnion<T>`

use crate::intrusive_ref_counts::{
    IntrusiveRefCounts, ReleaseStrongRefAction, ReleaseWeakRefAction,
};
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;
use std::ptr::NonNull;

/// An object whose lifetime is managed by the intrusive pointer family.
///
/// # Safety
///
/// `intrusive_ref_counts` must always return the stable counter belonging to
/// the allocation. Types selecting [`CompactIntrusiveOwner`] must only use
/// identity intrusive casts: the pointer view and the allocated type must be
/// identical when the final reference destroys the allocation.
pub unsafe trait IntrusiveObject {
    type Owner: IntrusiveOwnerStorage;

    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts;

    fn partial_destructor(&self) {}
}

pub trait IntrusiveStaticCast<Target: IntrusiveObject>: IntrusiveObject + Sized {
    fn intrusive_static_cast(ptr: NonNull<Self>) -> NonNull<Target>;
}

impl<T: IntrusiveObject> IntrusiveStaticCast<T> for T {
    fn intrusive_static_cast(ptr: NonNull<Self>) -> NonNull<T> {
        ptr
    }
}

pub trait IntrusiveDynamicCast<Target: IntrusiveObject>: IntrusiveObject + Sized {
    fn intrusive_dynamic_cast(ptr: NonNull<Self>) -> Option<NonNull<Target>>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SharedIntrusiveAdopt {
    IncrementStrong,
    NoIncrement,
}

#[derive(Clone, Copy)]
struct IntrusiveOps {
    destroy: unsafe fn(*mut ()),
    partial_destructor: unsafe fn(*mut ()),
}

impl IntrusiveOps {
    fn of<T: IntrusiveObject>() -> Self {
        Self {
            destroy: destroy_impl::<T>,
            partial_destructor: partial_destructor_impl::<T>,
        }
    }
}

#[derive(Clone, Copy)]
struct IntrusiveOwner {
    raw: NonNull<()>,
    ops: IntrusiveOps,
}

/// Per-handle owner metadata used by pointers which support cross-type casts.
#[derive(Clone, Copy)]
pub struct ErasedIntrusiveOwner(Option<IntrusiveOwner>);

/// Zero-sized owner policy for concrete intrusive objects such as
/// `SHAMapTreeNode`. Destruction is monomorphized from the pointer's `T`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CompactIntrusiveOwner;

/// Storage policy carried alongside an intrusive pointer.
///
/// # Safety
///
/// Implementations must destroy and partially destroy exactly the allocation
/// represented by `ptr`, at most once, and preserve that identity when copied.
pub unsafe trait IntrusiveOwnerStorage: Copy {
    fn empty() -> Self;

    fn for_ptr<T: IntrusiveObject<Owner = Self>>(ptr: NonNull<T>) -> Self;

    /// # Safety
    ///
    /// `ptr` must identify the live allocation captured by this owner state,
    /// and the intrusive counters must have selected final destruction.
    unsafe fn destroy<T: IntrusiveObject<Owner = Self>>(self, ptr: NonNull<T>);

    /// # Safety
    ///
    /// `ptr` must identify the live allocation captured by this owner state,
    /// and this must be the unique partial-destruction transition selected by
    /// its intrusive counters.
    unsafe fn partial_destructor<T: IntrusiveObject<Owner = Self>>(self, ptr: NonNull<T>);
}

unsafe impl IntrusiveOwnerStorage for ErasedIntrusiveOwner {
    fn empty() -> Self {
        Self(None)
    }

    fn for_ptr<T: IntrusiveObject<Owner = Self>>(ptr: NonNull<T>) -> Self {
        Self(Some(IntrusiveOwner::of(ptr)))
    }

    unsafe fn destroy<T: IntrusiveObject<Owner = Self>>(self, _ptr: NonNull<T>) {
        self.0
            .expect("intrusive pointer lost its erased owner metadata")
            .destroy();
    }

    unsafe fn partial_destructor<T: IntrusiveObject<Owner = Self>>(self, _ptr: NonNull<T>) {
        self.0
            .expect("intrusive pointer lost its erased owner metadata")
            .partial_destructor();
    }
}

unsafe impl IntrusiveOwnerStorage for CompactIntrusiveOwner {
    fn empty() -> Self {
        Self
    }

    fn for_ptr<T: IntrusiveObject<Owner = Self>>(_ptr: NonNull<T>) -> Self {
        Self
    }

    unsafe fn destroy<T: IntrusiveObject<Owner = Self>>(self, ptr: NonNull<T>) {
        // SAFETY: CompactIntrusiveOwner's contract requires the pointer view
        // to be the original concrete allocation type.
        destroy_impl::<T>(ptr.cast().as_ptr());
    }

    unsafe fn partial_destructor<T: IntrusiveObject<Owner = Self>>(self, ptr: NonNull<T>) {
        // SAFETY: same concrete-allocation invariant as `destroy`.
        partial_destructor_impl::<T>(ptr.cast().as_ptr());
    }
}

impl IntrusiveOwner {
    fn of<T: IntrusiveObject>(ptr: NonNull<T>) -> Self {
        Self {
            raw: ptr.cast(),
            ops: IntrusiveOps::of::<T>(),
        }
    }

    fn destroy(self) {
        // SAFETY: The owner stores the original allocation type and the
        // matching destroy function for that allocation.
        unsafe { (self.ops.destroy)(self.raw.as_ptr()) };
    }

    fn partial_destructor(self) {
        // SAFETY: The owner stores the original allocation type and the
        // matching partial-destructor function for that allocation.
        unsafe { (self.ops.partial_destructor)(self.raw.as_ptr()) };
    }
}

pub struct SharedIntrusive<T: IntrusiveObject> {
    ptr: Option<NonNull<T>>,
    owner: T::Owner,
    marker: PhantomData<T>,
}

pub struct WeakIntrusive<T: IntrusiveObject> {
    ptr: Option<NonNull<T>>,
    owner: T::Owner,
    marker: PhantomData<T>,
}

pub struct SharedWeakUnion<T: IntrusiveObject> {
    tagged_ptr: usize,
    owner: T::Owner,
    marker: PhantomData<T>,
}

impl<T: IntrusiveObject> Default for SharedIntrusive<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: IntrusiveObject> Default for WeakIntrusive<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: IntrusiveObject> Default for SharedWeakUnion<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: IntrusiveObject> SharedIntrusive<T> {
    pub fn new() -> Self {
        Self {
            ptr: None,
            owner: T::Owner::empty(),
            marker: PhantomData,
        }
    }

    pub fn is_null(&self) -> bool {
        self.ptr.is_none()
    }

    pub fn get(&self) -> Option<&T> {
        self.ptr.map(|ptr| {
            // SAFETY: A strong intrusive pointer guarantees the pointee stays
            // alive until this handle releases it.
            unsafe { ptr.as_ref() }
        })
    }

    pub fn use_count(&self) -> usize {
        self.get()
            .map_or(0, |value| value.intrusive_ref_counts().use_count())
    }

    pub fn reset(&mut self) {
        self.release_and_store(None, T::Owner::empty());
    }

    /// # Safety
    ///
    /// `ptr` must satisfy the same lifetime and initialization guarantees as
    /// [`SharedIntrusive::from_raw`].
    pub unsafe fn adopt(&mut self, ptr: *mut T, adopt: SharedIntrusiveAdopt) {
        let next = NonNull::new(ptr);
        if let Some(raw) = next
            && matches!(adopt, SharedIntrusiveAdopt::IncrementStrong)
        {
            // SAFETY: guaranteed by the caller contract for `adopt`.
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
        }
        self.release_and_store(next, next.map_or_else(T::Owner::empty, T::Owner::for_ptr));
    }

    pub fn downgrade(&self) -> WeakIntrusive<T> {
        WeakIntrusive::from_shared(self)
    }

    /// # Safety
    ///
    /// `ptr` must either be null or point to a valid intrusive object whose
    /// refcount storage remains alive for the lifetime represented by the
    /// returned handle. When `adopt` is `IncrementStrong`, the pointed-to value
    /// must already be initialized enough for intrusive refcount operations.
    pub unsafe fn from_raw(ptr: *mut T, adopt: SharedIntrusiveAdopt) -> Self {
        let ptr = NonNull::new(ptr);
        if let Some(raw) = ptr
            && matches!(adopt, SharedIntrusiveAdopt::IncrementStrong)
        {
            // SAFETY: `raw` came from the caller and is assumed valid for the
            // intrusive lifetime operations.
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
        }

        Self {
            ptr,
            owner: ptr.map_or_else(T::Owner::empty, T::Owner::for_ptr),
            marker: PhantomData,
        }
    }

    fn release_and_store(&mut self, next: Option<NonNull<T>>, next_owner: T::Owner) {
        let previous = mem::replace(&mut self.ptr, next);
        let previous_owner = mem::replace(&mut self.owner, next_owner);
        let Some(previous) = previous else {
            return;
        };

        let value = unsafe { previous.as_ref() };
        match value.intrusive_ref_counts().release_strong_ref() {
            ReleaseStrongRefAction::Noop => {}
            ReleaseStrongRefAction::Destroy => unsafe { previous_owner.destroy(previous) },
            ReleaseStrongRefAction::PartialDestroy => {
                unsafe { previous_owner.partial_destructor(previous) };
                value.intrusive_ref_counts().partial_destructor_finished();
            }
        }
    }

    pub fn static_pointer_cast<U>(&self) -> SharedIntrusive<U>
    where
        T: IntrusiveStaticCast<U>,
        U: IntrusiveObject<Owner = T::Owner>,
    {
        let Some(ptr) = self.ptr else {
            return SharedIntrusive::new();
        };

        unsafe { ptr.as_ref() }
            .intrusive_ref_counts()
            .add_strong_ref();

        let casted = T::intrusive_static_cast(ptr);
        SharedIntrusive {
            ptr: Some(casted),
            owner: self.owner,
            marker: PhantomData,
        }
    }

    pub fn static_pointer_cast_owned<U>(self) -> SharedIntrusive<U>
    where
        T: IntrusiveStaticCast<U>,
        U: IntrusiveObject<Owner = T::Owner>,
    {
        let mut value = mem::ManuallyDrop::new(self);
        let ptr = value.ptr.take().map(T::intrusive_static_cast);

        SharedIntrusive {
            ptr,
            owner: mem::replace(&mut value.owner, T::Owner::empty()),
            marker: PhantomData,
        }
    }

    /// Move this intrusive owner into a related target view without
    /// incrementing the strong count, matching the reference converting move
    /// constructor/assignment role for compatible intrusive pointer types.
    pub fn into_shared_intrusive<U>(self) -> SharedIntrusive<U>
    where
        T: IntrusiveStaticCast<U>,
        U: IntrusiveObject<Owner = T::Owner>,
    {
        self.static_pointer_cast_owned()
    }

    /// Rebind this intrusive pointer from a compatible shared owner by
    /// incrementing the strong count, matching the reference
    /// `SharedIntrusive::operator=(SharedIntrusive const&)` role for related
    /// types.
    pub fn assign_from_shared<Source>(&mut self, shared: &SharedIntrusive<Source>)
    where
        Source: IntrusiveStaticCast<T> + IntrusiveObject<Owner = T::Owner>,
    {
        let next = shared.ptr.map(Source::intrusive_static_cast);
        if let Some(raw) = next {
            // SAFETY: `raw` is still owned by the source strong handle and the
            // increment happens before this owner releases its previous value.
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
        }
        self.release_and_store(next, shared.owner);
    }

    /// Rebind this intrusive pointer by taking ownership from a compatible
    /// shared owner, matching the reference converting move-assignment role.
    pub fn assign_from_shared_owned<Source>(&mut self, shared: SharedIntrusive<Source>)
    where
        Source: IntrusiveStaticCast<T> + IntrusiveObject<Owner = T::Owner>,
    {
        let mut shared = mem::ManuallyDrop::new(shared);
        let next = shared.ptr.take().map(Source::intrusive_static_cast);
        let next_owner = mem::replace(&mut shared.owner, T::Owner::empty());
        self.release_and_store(next, next_owner);
    }

    pub fn from_borrowed_static_cast<U>(value: &SharedIntrusive<T>) -> SharedIntrusive<U>
    where
        T: IntrusiveStaticCast<U>,
        U: IntrusiveObject<Owner = T::Owner>,
    {
        value.static_pointer_cast()
    }

    pub fn from_owned_static_cast<U>(value: SharedIntrusive<T>) -> SharedIntrusive<U>
    where
        T: IntrusiveStaticCast<U>,
        U: IntrusiveObject<Owner = T::Owner>,
    {
        value.static_pointer_cast_owned()
    }

    pub fn dynamic_pointer_cast<U>(&self) -> SharedIntrusive<U>
    where
        T: IntrusiveDynamicCast<U>,
        U: IntrusiveObject<Owner = T::Owner>,
    {
        let Some(ptr) = self.ptr else {
            return SharedIntrusive::new();
        };

        let Some(casted) = T::intrusive_dynamic_cast(ptr) else {
            return SharedIntrusive::new();
        };

        unsafe { ptr.as_ref() }
            .intrusive_ref_counts()
            .add_strong_ref();

        SharedIntrusive {
            ptr: Some(casted),
            owner: self.owner,
            marker: PhantomData,
        }
    }

    pub fn from_borrowed_dynamic_cast<U>(value: &SharedIntrusive<T>) -> SharedIntrusive<U>
    where
        T: IntrusiveDynamicCast<U>,
        U: IntrusiveObject<Owner = T::Owner>,
    {
        value.dynamic_pointer_cast()
    }

    pub fn try_dynamic_pointer_cast_owned<U>(self) -> Result<SharedIntrusive<U>, Self>
    where
        T: IntrusiveDynamicCast<U>,
        U: IntrusiveObject<Owner = T::Owner>,
    {
        let mut value = mem::ManuallyDrop::new(self);
        let Some(ptr) = value.ptr.take() else {
            return Ok(SharedIntrusive::new());
        };

        let Some(casted) = T::intrusive_dynamic_cast(ptr) else {
            return Err(SharedIntrusive {
                ptr: Some(ptr),
                owner: mem::replace(&mut value.owner, T::Owner::empty()),
                marker: PhantomData,
            });
        };

        Ok(SharedIntrusive {
            ptr: Some(casted),
            owner: mem::replace(&mut value.owner, T::Owner::empty()),
            marker: PhantomData,
        })
    }

    pub fn from_owned_dynamic_cast<U>(value: SharedIntrusive<T>) -> Result<SharedIntrusive<U>, Self>
    where
        T: IntrusiveDynamicCast<U>,
        U: IntrusiveObject<Owner = T::Owner>,
    {
        value.try_dynamic_pointer_cast_owned()
    }
}

impl<T: IntrusiveObject> Clone for SharedIntrusive<T> {
    fn clone(&self) -> Self {
        if let Some(ptr) = self.ptr {
            unsafe { ptr.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
        }

        Self {
            ptr: self.ptr,
            owner: self.owner,
            marker: PhantomData,
        }
    }
}

impl<T: IntrusiveObject> Drop for SharedIntrusive<T> {
    fn drop(&mut self) {
        self.release_and_store(None, T::Owner::empty());
    }
}

impl<T: IntrusiveObject> Deref for SharedIntrusive<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.get()
            .expect("cannot dereference a null SharedIntrusive pointer")
    }
}

impl<T: IntrusiveObject> fmt::Debug for SharedIntrusive<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SharedIntrusive")
            .field("ptr", &self.ptr)
            .field("use_count", &self.use_count())
            .finish()
    }
}

impl<T: IntrusiveObject> WeakIntrusive<T> {
    pub fn new() -> Self {
        Self {
            ptr: None,
            owner: T::Owner::empty(),
            marker: PhantomData,
        }
    }

    pub fn from_shared(shared: &SharedIntrusive<T>) -> Self {
        let ptr = shared.ptr;
        if let Some(raw) = ptr {
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_weak_ref();
        }

        Self {
            ptr,
            owner: shared.owner,
            marker: PhantomData,
        }
    }

    /// Rebind this weak intrusive pointer from a compatible shared owner,
    /// matching the reference `WeakIntrusive::operator=(SharedIntrusive const&)`
    /// role for related types.
    pub fn assign_from_shared<Source>(&mut self, shared: &SharedIntrusive<Source>)
    where
        Source: IntrusiveStaticCast<T> + IntrusiveObject<Owner = T::Owner>,
    {
        self.release_no_store();
        self.ptr = shared.ptr.map(Source::intrusive_static_cast);
        self.owner = shared.owner;
        if let Some(raw) = self.ptr {
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_weak_ref();
        }
    }

    pub fn lock(&self) -> SharedIntrusive<T> {
        let Some(ptr) = self.ptr else {
            return SharedIntrusive::new();
        };

        let value = unsafe { ptr.as_ref() };
        if value.intrusive_ref_counts().checkout_strong_ref_from_weak() {
            SharedIntrusive {
                ptr: Some(ptr),
                owner: self.owner,
                marker: PhantomData,
            }
        } else {
            SharedIntrusive::new()
        }
    }

    pub fn expired(&self) -> bool {
        self.ptr
            .is_none_or(|ptr| unsafe { ptr.as_ref() }.intrusive_ref_counts().expired())
    }

    pub fn reset(&mut self) {
        self.release_no_store();
        self.ptr = None;
        self.owner = T::Owner::empty();
    }

    /// # Safety
    ///
    /// `ptr` must be null or point to a valid intrusive object whose refcount
    /// storage remains alive for the lifetime represented by this weak handle.
    pub unsafe fn adopt(&mut self, ptr: *mut T) {
        self.release_no_store();
        self.ptr = NonNull::new(ptr);
        self.owner = self.ptr.map_or_else(T::Owner::empty, T::Owner::for_ptr);
        if let Some(raw) = self.ptr {
            // SAFETY: guaranteed by the caller contract for `adopt`.
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_weak_ref();
        }
    }

    fn release_no_store(&mut self) {
        let Some(ptr) = self.ptr else {
            return;
        };
        let value = unsafe { ptr.as_ref() };
        if matches!(
            value.intrusive_ref_counts().release_weak_ref(),
            ReleaseWeakRefAction::Destroy
        ) {
            unsafe { self.owner.destroy(ptr) };
        }
    }
}

impl<Target, Source> From<&SharedIntrusive<Source>> for WeakIntrusive<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject<Owner = Source::Owner>,
{
    fn from(value: &SharedIntrusive<Source>) -> Self {
        let ptr = value.ptr.map(Source::intrusive_static_cast);
        if let Some(raw) = ptr {
            // SAFETY: `raw` came from a live intrusive strong owner and the
            // weak handle immediately increments the weak count.
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_weak_ref();
        }

        Self {
            ptr,
            owner: value.owner,
            marker: PhantomData,
        }
    }
}

impl<T: IntrusiveObject> From<&SharedIntrusive<T>> for bool {
    fn from(value: &SharedIntrusive<T>) -> Self {
        !value.is_null()
    }
}

impl<T: IntrusiveObject> From<&WeakIntrusive<T>> for bool {
    fn from(value: &WeakIntrusive<T>) -> Self {
        !value.expired()
    }
}

impl<T: IntrusiveObject> From<&SharedWeakUnion<T>> for bool {
    fn from(value: &SharedWeakUnion<T>) -> Self {
        value.get().is_some()
    }
}

impl<T: IntrusiveObject> SharedWeakUnion<T> {
    const TAG_MASK: usize = 1;
    const PTR_MASK: usize = !Self::TAG_MASK;

    pub fn new() -> Self {
        Self {
            tagged_ptr: 0,
            owner: T::Owner::empty(),
            marker: PhantomData,
        }
    }

    pub fn get_strong(&self) -> SharedIntrusive<T> {
        let Some(ptr) = self.unsafe_get_raw_ptr() else {
            return SharedIntrusive::new();
        };

        if self.is_strong() {
            unsafe { ptr.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
            SharedIntrusive {
                ptr: Some(ptr),
                owner: self.owner,
                marker: PhantomData,
            }
        } else {
            SharedIntrusive::new()
        }
    }

    pub fn reset(&mut self) {
        self.unsafe_release_no_store();
        self.unsafe_set_raw_ptr(None, RefStrength::Strong);
        self.owner = T::Owner::empty();
    }

    pub fn get(&self) -> Option<&T> {
        if self.is_strong() {
            self.unsafe_get_raw_ptr().map(|ptr| unsafe { ptr.as_ref() })
        } else {
            None
        }
    }

    pub fn use_count(&self) -> usize {
        self.get()
            .map_or(0, |value| value.intrusive_ref_counts().use_count())
    }

    pub fn expired(&self) -> bool {
        self.unsafe_get_raw_ptr()
            .is_none_or(|ptr| unsafe { ptr.as_ref() }.intrusive_ref_counts().expired())
    }

    pub fn lock(&self) -> SharedIntrusive<T> {
        let Some(ptr) = self.unsafe_get_raw_ptr() else {
            return SharedIntrusive::new();
        };

        if self.is_strong() {
            unsafe { ptr.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
            return SharedIntrusive {
                ptr: Some(ptr),
                owner: self.owner,
                marker: PhantomData,
            };
        }

        let value = unsafe { ptr.as_ref() };
        if value.intrusive_ref_counts().checkout_strong_ref_from_weak() {
            SharedIntrusive {
                ptr: Some(ptr),
                owner: self.owner,
                marker: PhantomData,
            }
        } else {
            SharedIntrusive::new()
        }
    }

    pub fn is_strong(&self) -> bool {
        (self.tagged_ptr & Self::TAG_MASK) == 0
    }

    pub fn is_weak(&self) -> bool {
        !self.is_strong()
    }

    pub fn convert_to_strong(&mut self) -> bool {
        if self.is_strong() {
            return true;
        }

        let Some(ptr) = self.unsafe_get_raw_ptr() else {
            return false;
        };

        let value = unsafe { ptr.as_ref() };
        if value.intrusive_ref_counts().checkout_strong_ref_from_weak() {
            let action = value.intrusive_ref_counts().release_weak_ref();
            debug_assert_eq!(action, ReleaseWeakRefAction::Noop);
            self.unsafe_set_raw_ptr(Some(ptr), RefStrength::Strong);
            true
        } else {
            false
        }
    }

    pub fn convert_to_weak(&mut self) -> bool {
        if self.is_weak() {
            return true;
        }

        let Some(ptr) = self.unsafe_get_raw_ptr() else {
            return false;
        };

        let value = unsafe { ptr.as_ref() };
        match value.intrusive_ref_counts().add_weak_release_strong_ref() {
            ReleaseStrongRefAction::Noop => {}
            ReleaseStrongRefAction::Destroy => {
                debug_assert!(false, "cannot destroy a freshly added weak ref");
                unsafe { self.owner.destroy(ptr) };
                self.unsafe_set_raw_ptr(None, RefStrength::Strong);
                self.owner = T::Owner::empty();
                return true;
            }
            ReleaseStrongRefAction::PartialDestroy => {
                unsafe { self.owner.partial_destructor(ptr) };
                value.intrusive_ref_counts().partial_destructor_finished();
            }
        }

        self.unsafe_set_raw_ptr(Some(ptr), RefStrength::Weak);
        true
    }

    /// Rebind this union from a compatible shared owner while retaining a
    /// strong representation, matching the reference borrowed strong assignment
    /// role.
    pub fn assign_from_shared<Source>(&mut self, shared: &SharedIntrusive<Source>)
    where
        Source: IntrusiveStaticCast<T> + IntrusiveObject<Owner = T::Owner>,
    {
        self.unsafe_release_no_store();
        let ptr = shared.ptr.map(Source::intrusive_static_cast);
        if let Some(raw) = ptr {
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
        }
        self.unsafe_set_raw_ptr(ptr, RefStrength::Strong);
        self.owner = shared.owner;
    }

    /// Rebind this union by taking ownership from a compatible shared owner,
    /// matching the reference move-assignment role for strong intrusive inputs.
    pub fn assign_from_shared_owned<Source>(&mut self, shared: SharedIntrusive<Source>)
    where
        Source: IntrusiveStaticCast<T> + IntrusiveObject<Owner = T::Owner>,
    {
        self.unsafe_release_no_store();
        let mut shared = mem::ManuallyDrop::new(shared);
        let ptr = shared.ptr.take().map(Source::intrusive_static_cast);
        self.unsafe_set_raw_ptr(ptr, RefStrength::Strong);
        self.owner = mem::replace(&mut shared.owner, T::Owner::empty());
    }

    fn ensure_alignment() {
        assert!(
            std::mem::align_of::<T>() >= 2,
            "SharedWeakUnion requires T alignment >= 2"
        );
    }

    fn unsafe_get_raw_ptr(&self) -> Option<NonNull<T>> {
        NonNull::new((self.tagged_ptr & Self::PTR_MASK) as *mut T)
    }

    fn unsafe_set_raw_ptr(&mut self, ptr: Option<NonNull<T>>, strength: RefStrength) {
        self.tagged_ptr = ptr.map_or(0, |raw| {
            Self::ensure_alignment();
            let tagged = raw.as_ptr() as usize;
            match strength {
                RefStrength::Strong => tagged,
                RefStrength::Weak => tagged | Self::TAG_MASK,
            }
        });
    }

    fn unsafe_release_no_store(&mut self) {
        let Some(ptr) = self.unsafe_get_raw_ptr() else {
            return;
        };
        let value = unsafe { ptr.as_ref() };
        if self.is_strong() {
            match value.intrusive_ref_counts().release_strong_ref() {
                ReleaseStrongRefAction::Noop => {}
                ReleaseStrongRefAction::Destroy => unsafe { self.owner.destroy(ptr) },
                ReleaseStrongRefAction::PartialDestroy => {
                    unsafe { self.owner.partial_destructor(ptr) };
                    value.intrusive_ref_counts().partial_destructor_finished();
                }
            }
        } else if matches!(
            value.intrusive_ref_counts().release_weak_ref(),
            ReleaseWeakRefAction::Destroy
        ) {
            unsafe { self.owner.destroy(ptr) };
        }
    }
}

impl<T: IntrusiveObject> Clone for SharedWeakUnion<T> {
    fn clone(&self) -> Self {
        if let Some(raw) = self.unsafe_get_raw_ptr() {
            let value = unsafe { raw.as_ref() };
            if self.is_strong() {
                value.intrusive_ref_counts().add_strong_ref();
            } else {
                value.intrusive_ref_counts().add_weak_ref();
            }
        }

        Self {
            tagged_ptr: self.tagged_ptr,
            owner: self.owner,
            marker: PhantomData,
        }
    }
}

impl<T: IntrusiveObject> Drop for SharedWeakUnion<T> {
    fn drop(&mut self) {
        self.unsafe_release_no_store();
    }
}

impl<T: IntrusiveObject> fmt::Debug for SharedWeakUnion<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SharedWeakUnion")
            .field("tagged_ptr", &self.tagged_ptr)
            .field("is_strong", &self.is_strong())
            .finish()
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StaticCastTagSharedIntrusive;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DynamicCastTagSharedIntrusive;

impl<Target, Source> From<&SharedIntrusive<Source>> for SharedWeakUnion<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject<Owner = Source::Owner>,
{
    fn from(value: &SharedIntrusive<Source>) -> Self {
        let ptr = value.ptr.map(Source::intrusive_static_cast);
        if let Some(raw) = ptr {
            // SAFETY: `raw` stays alive while the added strong ref is held by
            // the returned union.
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
        }

        let mut result = Self::new();
        result.unsafe_set_raw_ptr(ptr, RefStrength::Strong);
        result.owner = value.owner;
        result
    }
}

impl<Target, Source> From<SharedIntrusive<Source>> for SharedWeakUnion<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject<Owner = Source::Owner>,
{
    fn from(value: SharedIntrusive<Source>) -> Self {
        let mut value = mem::ManuallyDrop::new(value);
        let ptr = value.ptr.take().map(Source::intrusive_static_cast);

        let mut result = Self::new();
        result.unsafe_set_raw_ptr(ptr, RefStrength::Strong);
        result.owner = value.owner;
        result
    }
}

impl<T: IntrusiveObject> From<&WeakIntrusive<T>> for SharedWeakUnion<T> {
    fn from(value: &WeakIntrusive<T>) -> Self {
        let ptr = value.ptr;
        if let Some(raw) = ptr {
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_weak_ref();
        }

        let mut result = Self::new();
        result.unsafe_set_raw_ptr(ptr, RefStrength::Weak);
        result.owner = value.owner;
        result
    }
}

impl<Target, Source> From<&SharedIntrusive<Source>> for SharedIntrusive<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject<Owner = Source::Owner>,
{
    fn from(value: &SharedIntrusive<Source>) -> Self {
        value.static_pointer_cast()
    }
}

impl<Target, Source> From<(StaticCastTagSharedIntrusive, &SharedIntrusive<Source>)>
    for SharedIntrusive<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject<Owner = Source::Owner>,
{
    fn from((_, value): (StaticCastTagSharedIntrusive, &SharedIntrusive<Source>)) -> Self {
        value.static_pointer_cast()
    }
}

impl<Target, Source> From<(StaticCastTagSharedIntrusive, SharedIntrusive<Source>)>
    for SharedIntrusive<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject<Owner = Source::Owner>,
{
    fn from((_, value): (StaticCastTagSharedIntrusive, SharedIntrusive<Source>)) -> Self {
        value.static_pointer_cast_owned()
    }
}

impl<Target, Source> From<(DynamicCastTagSharedIntrusive, &SharedIntrusive<Source>)>
    for SharedIntrusive<Target>
where
    Source: IntrusiveDynamicCast<Target> + IntrusiveObject,
    Target: IntrusiveObject<Owner = Source::Owner>,
{
    fn from((_, value): (DynamicCastTagSharedIntrusive, &SharedIntrusive<Source>)) -> Self {
        value.dynamic_pointer_cast()
    }
}

impl<Target, Source> TryFrom<(DynamicCastTagSharedIntrusive, SharedIntrusive<Source>)>
    for SharedIntrusive<Target>
where
    Source: IntrusiveDynamicCast<Target> + IntrusiveObject,
    Target: IntrusiveObject<Owner = Source::Owner>,
{
    type Error = SharedIntrusive<Source>;

    fn try_from(
        (_, value): (DynamicCastTagSharedIntrusive, SharedIntrusive<Source>),
    ) -> Result<Self, Self::Error> {
        value.try_dynamic_pointer_cast_owned()
    }
}

impl<T: IntrusiveObject> Clone for WeakIntrusive<T> {
    fn clone(&self) -> Self {
        if let Some(ptr) = self.ptr {
            unsafe { ptr.as_ref() }
                .intrusive_ref_counts()
                .add_weak_ref();
        }

        Self {
            ptr: self.ptr,
            owner: self.owner,
            marker: PhantomData,
        }
    }
}

impl<T: IntrusiveObject> Drop for WeakIntrusive<T> {
    fn drop(&mut self) {
        self.release_no_store();
    }
}

impl<T: IntrusiveObject> fmt::Debug for WeakIntrusive<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WeakIntrusive")
            .field("ptr", &self.ptr)
            .field("expired", &self.expired())
            .finish()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RefStrength {
    Strong,
    Weak,
}

fn destroy_impl<T: IntrusiveObject>(ptr: *mut ()) {
    // SAFETY: `ptr` was created from a `Box<T>` by `IntrusiveOwner::of`.
    unsafe {
        drop(Box::from_raw(ptr.cast::<T>()));
    }
}

fn partial_destructor_impl<T: IntrusiveObject>(ptr: *mut ()) {
    // SAFETY: `ptr` points to the original allocation used to create the
    // intrusive owner, so it is valid to reinterpret it as `T`.
    let value = unsafe { &*(ptr.cast::<T>()) };
    value.partial_destructor();
}

pub fn static_pointer_cast<Target, Source>(
    value: &SharedIntrusive<Source>,
) -> SharedIntrusive<Target>
where
    Source: IntrusiveStaticCast<Target>,
    Target: IntrusiveObject<Owner = Source::Owner>,
{
    value.static_pointer_cast()
}

pub fn dynamic_pointer_cast<Target, Source>(
    value: &SharedIntrusive<Source>,
) -> SharedIntrusive<Target>
where
    Source: IntrusiveDynamicCast<Target>,
    Target: IntrusiveObject<Owner = Source::Owner>,
{
    value.dynamic_pointer_cast()
}

pub fn make_shared_intrusive<T: IntrusiveObject>(value: T) -> SharedIntrusive<T> {
    let raw = Box::into_raw(Box::new(value));
    unsafe { SharedIntrusive::from_raw(raw, SharedIntrusiveAdopt::NoIncrement) }
}

unsafe impl<T> Send for SharedIntrusive<T> where T: IntrusiveObject + Send + Sync {}

unsafe impl<T> Sync for SharedIntrusive<T> where T: IntrusiveObject + Send + Sync {}

unsafe impl<T> Send for WeakIntrusive<T> where T: IntrusiveObject + Send + Sync {}

unsafe impl<T> Sync for WeakIntrusive<T> where T: IntrusiveObject + Send + Sync {}

unsafe impl<T> Send for SharedWeakUnion<T> where T: IntrusiveObject + Send + Sync {}

unsafe impl<T> Sync for SharedWeakUnion<T> where T: IntrusiveObject + Send + Sync {}

#[cfg(test)]
mod tests {
    use super::{
        IntrusiveObject, SharedIntrusive, SharedWeakUnion, WeakIntrusive, make_shared_intrusive,
    };
    use crate::intrusive_ref_counts::IntrusiveRefCounts;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicU8, Ordering};

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum LifecycleState {
        Alive = 1,
        PartiallyDeleted = 2,
        Deleted = 3,
    }

    impl LifecycleState {
        fn load(state: &AtomicU8) -> Self {
            match state.load(Ordering::SeqCst) {
                1 => Self::Alive,
                2 => Self::PartiallyDeleted,
                3 => Self::Deleted,
                other => panic!("unexpected lifecycle state: {other}"),
            }
        }
    }

    #[derive(Debug)]
    struct TrackingState {
        lifecycle: AtomicU8,
    }

    impl TrackingState {
        fn new() -> Self {
            Self {
                lifecycle: AtomicU8::new(LifecycleState::Alive as u8),
            }
        }
    }

    #[derive(Debug)]
    struct TestNode {
        ref_counts: IntrusiveRefCounts,
        tracking: Arc<TrackingState>,
    }

    impl TestNode {
        fn new(tracking: Arc<TrackingState>) -> Self {
            Self {
                ref_counts: IntrusiveRefCounts::new(),
                tracking,
            }
        }
    }

    unsafe impl IntrusiveObject for TestNode {
        type Owner = super::ErasedIntrusiveOwner;

        fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
            &self.ref_counts
        }

        fn partial_destructor(&self) {
            self.tracking
                .lifecycle
                .store(LifecycleState::PartiallyDeleted as u8, Ordering::SeqCst);
        }
    }

    impl Drop for TestNode {
        fn drop(&mut self) {
            self.tracking
                .lifecycle
                .store(LifecycleState::Deleted as u8, Ordering::SeqCst);
        }
    }

    #[test]
    fn shared_intrusive_keeps_object_alive_until_last_strong_release() {
        let tracking = Arc::new(TrackingState::new());
        let shared = make_shared_intrusive(TestNode::new(Arc::clone(&tracking)));
        let clones: Vec<SharedIntrusive<TestNode>> = (0..10).map(|_| shared.clone()).collect();

        assert_eq!(shared.use_count(), 11);
        drop(clones);
        assert_eq!(
            LifecycleState::load(&tracking.lifecycle),
            LifecycleState::Alive
        );

        drop(shared);
        assert_eq!(
            LifecycleState::load(&tracking.lifecycle),
            LifecycleState::Deleted
        );
    }

    #[test]
    fn shared_intrusive_adopt_and_bool_match_cpp_role() {
        let tracking = Arc::new(TrackingState::new());
        let mut shared: SharedIntrusive<TestNode> = SharedIntrusive::new();
        let raw = Box::into_raw(Box::new(TestNode::new(Arc::clone(&tracking))));

        unsafe { shared.adopt(raw, super::SharedIntrusiveAdopt::NoIncrement) };

        assert!(bool::from(&shared));
        assert!(!shared.is_null());
        assert_eq!(shared.use_count(), 1);

        shared.reset();
        assert_eq!(
            LifecycleState::load(&tracking.lifecycle),
            LifecycleState::Deleted
        );
    }

    #[test]
    fn weak_intrusive_allows_lock_before_partial_destruction_only() {
        let tracking = Arc::new(TrackingState::new());
        let mut shared = make_shared_intrusive(TestNode::new(Arc::clone(&tracking)));
        let mut weak = WeakIntrusive::from_shared(&shared);

        let strong_from_weak = weak.lock();
        assert!(!strong_from_weak.is_null());
        assert_eq!(strong_from_weak.use_count(), 2);

        shared.reset();
        assert_eq!(
            LifecycleState::load(&tracking.lifecycle),
            LifecycleState::Alive
        );

        drop(strong_from_weak);
        assert_eq!(
            LifecycleState::load(&tracking.lifecycle),
            LifecycleState::PartiallyDeleted
        );
        assert!(weak.expired());
        assert!(weak.lock().is_null());

        weak.reset();
        assert_eq!(
            LifecycleState::load(&tracking.lifecycle),
            LifecycleState::Deleted
        );
    }

    #[test]
    fn weak_intrusive_adopt_adds_weak_reference() {
        let tracking = Arc::new(TrackingState::new());
        let shared = make_shared_intrusive(TestNode::new(Arc::clone(&tracking)));
        let raw = shared
            .get()
            .map(|value| value as *const TestNode as *mut TestNode)
            .expect("shared pointer should be seated");
        let mut weak = WeakIntrusive::new();

        unsafe { weak.adopt(raw) };

        assert!(bool::from(&weak));
        assert!(!weak.expired());
        assert!(!weak.lock().is_null());

        drop(shared);
        assert!(weak.expired());
        weak.reset();
        assert_eq!(
            LifecycleState::load(&tracking.lifecycle),
            LifecycleState::Deleted
        );
    }

    #[test]
    fn shared_weak_union_basic_lifecycle_roles() {
        let tracking = Arc::new(TrackingState::new());
        let mut strong =
            SharedWeakUnion::from(make_shared_intrusive(TestNode::new(Arc::clone(&tracking))));

        assert!(strong.is_strong());
        assert_eq!(strong.use_count(), 1);

        let mut weak = strong.clone();
        assert!(weak.is_strong());
        assert_eq!(strong.use_count(), 2);

        assert!(weak.convert_to_weak());
        assert!(weak.is_weak());
        assert_eq!(strong.use_count(), 1);

        let mut restored = weak.clone();
        assert!(restored.is_weak());
        assert_eq!(strong.use_count(), 1);
        assert!(restored.convert_to_strong());
        assert!(restored.is_strong());
        assert_eq!(strong.use_count(), 2);

        strong.reset();
        assert_eq!(
            LifecycleState::load(&tracking.lifecycle),
            LifecycleState::Alive
        );
        assert_eq!(restored.use_count(), 1);
        assert!(!weak.expired());

        restored.reset();
        assert_eq!(
            LifecycleState::load(&tracking.lifecycle),
            LifecycleState::PartiallyDeleted
        );
        assert!(weak.expired());
        assert!(!weak.convert_to_strong());
        assert!(weak.is_weak());

        weak.reset();
        assert_eq!(
            LifecycleState::load(&tracking.lifecycle),
            LifecycleState::Deleted
        );
    }
}
