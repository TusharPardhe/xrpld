//! Intrusive-pointer ownership types for the shared and weak parts of
//! `xrpl/basics/IntrusivePointer.h`.

use crate::intrusive_ref_counts::{
    IntrusiveRefCounts, ReleaseStrongRefAction, ReleaseWeakRefAction,
};
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::num::NonZeroUsize;
use std::ops::Deref;
use std::ptr::NonNull;

pub trait IntrusiveObject {
    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts;

    fn partial_destructor(&self) {}

    fn initialize_intrusive_owner<Owner: IntrusiveObject>(&self, owner: NonNull<Owner>) {
        self.intrusive_ref_counts().initialize_owner_metadata(owner);
    }

    fn dispatch_intrusive_partial_destroy(&self) {
        self.intrusive_ref_counts().dispatch_partial_destroy();
    }

    fn dispatch_intrusive_final_destroy(&self) {
        self.intrusive_ref_counts().dispatch_final_destroy();
    }
}

unsafe fn dispatch_partial<T: IntrusiveObject>(ptr: NonNull<T>) {
    unsafe { ptr.as_ref() }.dispatch_intrusive_partial_destroy();
}

unsafe fn dispatch_final<T: IntrusiveObject>(ptr: NonNull<T>) {
    unsafe { ptr.as_ref() }.dispatch_intrusive_final_destroy();
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

const NULL_SENTINEL: usize = 1;

fn assert_intrusive_alignment<T>(ptr: NonNull<T>) {
    assert!(
        std::mem::align_of::<T>() >= 2 && (ptr.as_ptr() as usize & 1) == 0,
        "intrusive objects and cast views must have alignment >= 2"
    );
}

fn null_handle() -> NonZeroUsize {
    // SAFETY: the sentinel is deliberately non-zero and never represents an object.
    unsafe { NonZeroUsize::new_unchecked(NULL_SENTINEL) }
}

pub struct SharedIntrusive<T: IntrusiveObject> {
    ptr: NonZeroUsize,
    marker: PhantomData<T>,
}

pub struct WeakIntrusive<T: IntrusiveObject> {
    ptr: NonZeroUsize,
    marker: PhantomData<T>,
}

pub struct SharedWeakUnion<T: IntrusiveObject> {
    tagged_ptr: usize,
    marker: PhantomData<T>,
}

const _: () = assert!(std::mem::size_of::<SharedIntrusive<PointerLayoutProbe>>() == 8);

struct PointerLayoutProbe;
impl IntrusiveObject for PointerLayoutProbe {
    fn intrusive_ref_counts(&self) -> &IntrusiveRefCounts {
        unreachable!()
    }
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
    pub const fn new() -> Self {
        Self {
            ptr: unsafe { NonZeroUsize::new_unchecked(NULL_SENTINEL) },
            marker: PhantomData,
        }
    }

    fn pointer_bits(ptr: NonNull<T>) -> NonZeroUsize {
        assert_intrusive_alignment(ptr);
        NonZeroUsize::new(ptr.as_ptr() as usize).expect("non-null intrusive pointer")
    }

    fn from_ptr(ptr: NonNull<T>) -> Self {
        Self {
            ptr: Self::pointer_bits(ptr),
            marker: PhantomData,
        }
    }

    fn raw(&self) -> Option<NonNull<T>> {
        (self.ptr.get() != NULL_SENTINEL).then(|| {
            // SAFETY: all non-sentinel values are created from NonNull<T>.
            unsafe { NonNull::new_unchecked(self.ptr.get() as *mut T) }
        })
    }

    pub fn is_null(&self) -> bool {
        self.ptr.get() == NULL_SENTINEL
    }

    pub fn get(&self) -> Option<&T> {
        self.raw().map(|ptr| unsafe { ptr.as_ref() })
    }

    pub fn use_count(&self) -> usize {
        self.get()
            .map_or(0, |value| value.intrusive_ref_counts().use_count())
    }

    pub fn reset(&mut self) {
        self.release_and_store(None);
    }

    /// # Safety
    /// `ptr` must satisfy the same lifetime and initialization guarantees as
    /// [`SharedIntrusive::from_raw`].
    pub unsafe fn adopt(&mut self, ptr: *mut T, adopt: SharedIntrusiveAdopt) {
        let next = NonNull::new(ptr);
        if let Some(raw) = next {
            assert_intrusive_alignment(raw);
            let object = unsafe { raw.as_ref() };
            let counts = object.intrusive_ref_counts();
            object.initialize_intrusive_owner(raw);
            if matches!(adopt, SharedIntrusiveAdopt::IncrementStrong) {
                counts.add_strong_ref();
            }
        }
        self.release_and_store(next);
    }

    pub fn downgrade(&self) -> WeakIntrusive<T> {
        WeakIntrusive::from_shared(self)
    }

    /// # Safety
    /// `ptr` must either be null or point to a valid intrusive object whose
    /// refcount storage remains alive for the lifetime represented by the
    /// returned handle.
    pub unsafe fn from_raw(ptr: *mut T, adopt: SharedIntrusiveAdopt) -> Self {
        let Some(raw) = NonNull::new(ptr) else {
            return Self::new();
        };
        assert_intrusive_alignment(raw);
        let object = unsafe { raw.as_ref() };
        let counts = object.intrusive_ref_counts();
        object.initialize_intrusive_owner(raw);
        if matches!(adopt, SharedIntrusiveAdopt::IncrementStrong) {
            counts.add_strong_ref();
        }
        Self::from_ptr(raw)
    }

    /// Creates a public view over `ptr` while recording `owner` as the original
    /// concrete allocation. This supports compact polymorphic allocations whose
    /// public intrusive type is a prefix/base view.
    ///
    /// # Safety
    /// `ptr` must be a valid view into `owner`; both must share the same
    /// intrusive control word, and `owner` must be the original Box allocation.
    pub unsafe fn from_raw_with_owner<Owner: IntrusiveObject>(
        ptr: *mut T,
        owner: *mut Owner,
        adopt: SharedIntrusiveAdopt,
    ) -> Self {
        let Some(raw) = NonNull::new(ptr) else {
            return Self::new();
        };
        let owner = NonNull::new(owner).expect("non-null intrusive owner");
        assert_intrusive_alignment(raw);
        assert_intrusive_alignment(owner);
        let object = unsafe { raw.as_ref() };
        let counts = object.intrusive_ref_counts();
        object.initialize_intrusive_owner(owner);
        if matches!(adopt, SharedIntrusiveAdopt::IncrementStrong) {
            counts.add_strong_ref();
        }
        Self::from_ptr(raw)
    }

    fn release_and_store(&mut self, next: Option<NonNull<T>>) {
        let previous = self.raw();
        self.ptr = next.map_or_else(null_handle, Self::pointer_bits);
        let Some(previous) = previous else {
            return;
        };
        let counts = unsafe { previous.as_ref() }.intrusive_ref_counts();
        match counts.release_strong_ref() {
            ReleaseStrongRefAction::Noop => {}
            ReleaseStrongRefAction::Destroy => unsafe { dispatch_final(previous) },
            ReleaseStrongRefAction::PartialDestroy => unsafe { dispatch_partial(previous) },
        }
    }

    pub fn static_pointer_cast<U>(&self) -> SharedIntrusive<U>
    where
        T: IntrusiveStaticCast<U>,
        U: IntrusiveObject,
    {
        let Some(ptr) = self.raw() else {
            return SharedIntrusive::new();
        };
        unsafe { ptr.as_ref() }
            .intrusive_ref_counts()
            .add_strong_ref();
        SharedIntrusive::from_ptr(T::intrusive_static_cast(ptr))
    }

    pub fn static_pointer_cast_owned<U>(self) -> SharedIntrusive<U>
    where
        T: IntrusiveStaticCast<U>,
        U: IntrusiveObject,
    {
        let value = mem::ManuallyDrop::new(self);
        match value.raw() {
            Some(ptr) => SharedIntrusive::from_ptr(T::intrusive_static_cast(ptr)),
            None => SharedIntrusive::new(),
        }
    }

    pub fn into_shared_intrusive<U>(self) -> SharedIntrusive<U>
    where
        T: IntrusiveStaticCast<U>,
        U: IntrusiveObject,
    {
        self.static_pointer_cast_owned()
    }

    pub fn assign_from_shared<Source>(&mut self, shared: &SharedIntrusive<Source>)
    where
        Source: IntrusiveStaticCast<T> + IntrusiveObject,
    {
        let next = shared.raw().map(Source::intrusive_static_cast);
        if let Some(raw) = next {
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
        }
        self.release_and_store(next);
    }

    pub fn assign_from_shared_owned<Source>(&mut self, shared: SharedIntrusive<Source>)
    where
        Source: IntrusiveStaticCast<T> + IntrusiveObject,
    {
        let shared = mem::ManuallyDrop::new(shared);
        self.release_and_store(shared.raw().map(Source::intrusive_static_cast));
    }

    pub fn from_borrowed_static_cast<U>(value: &SharedIntrusive<T>) -> SharedIntrusive<U>
    where
        T: IntrusiveStaticCast<U>,
        U: IntrusiveObject,
    {
        value.static_pointer_cast()
    }

    pub fn from_owned_static_cast<U>(value: SharedIntrusive<T>) -> SharedIntrusive<U>
    where
        T: IntrusiveStaticCast<U>,
        U: IntrusiveObject,
    {
        value.static_pointer_cast_owned()
    }

    pub fn dynamic_pointer_cast<U>(&self) -> SharedIntrusive<U>
    where
        T: IntrusiveDynamicCast<U>,
        U: IntrusiveObject,
    {
        let Some(ptr) = self.raw() else {
            return SharedIntrusive::new();
        };
        let Some(casted) = T::intrusive_dynamic_cast(ptr) else {
            return SharedIntrusive::new();
        };
        unsafe { ptr.as_ref() }
            .intrusive_ref_counts()
            .add_strong_ref();
        SharedIntrusive::from_ptr(casted)
    }

    pub fn from_borrowed_dynamic_cast<U>(value: &SharedIntrusive<T>) -> SharedIntrusive<U>
    where
        T: IntrusiveDynamicCast<U>,
        U: IntrusiveObject,
    {
        value.dynamic_pointer_cast()
    }

    pub fn try_dynamic_pointer_cast_owned<U>(self) -> Result<SharedIntrusive<U>, Self>
    where
        T: IntrusiveDynamicCast<U>,
        U: IntrusiveObject,
    {
        let value = mem::ManuallyDrop::new(self);
        let Some(ptr) = value.raw() else {
            return Ok(SharedIntrusive::new());
        };
        match T::intrusive_dynamic_cast(ptr) {
            Some(casted) => Ok(SharedIntrusive::from_ptr(casted)),
            None => Err(SharedIntrusive::from_ptr(ptr)),
        }
    }

    pub fn from_owned_dynamic_cast<U>(value: SharedIntrusive<T>) -> Result<SharedIntrusive<U>, Self>
    where
        T: IntrusiveDynamicCast<U>,
        U: IntrusiveObject,
    {
        value.try_dynamic_pointer_cast_owned()
    }
}

impl<T: IntrusiveObject> Clone for SharedIntrusive<T> {
    fn clone(&self) -> Self {
        if let Some(ptr) = self.raw() {
            unsafe { ptr.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
        }
        Self {
            ptr: self.ptr,
            marker: PhantomData,
        }
    }
}

impl<T: IntrusiveObject> Drop for SharedIntrusive<T> {
    fn drop(&mut self) {
        self.release_and_store(None);
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
            .field("ptr", &self.raw())
            .field("use_count", &self.use_count())
            .finish()
    }
}

impl<T: IntrusiveObject> WeakIntrusive<T> {
    pub const fn new() -> Self {
        Self {
            ptr: unsafe { NonZeroUsize::new_unchecked(NULL_SENTINEL) },
            marker: PhantomData,
        }
    }

    fn pointer_bits(ptr: NonNull<T>) -> NonZeroUsize {
        assert_intrusive_alignment(ptr);
        NonZeroUsize::new(ptr.as_ptr() as usize).expect("non-null intrusive pointer")
    }

    fn from_ptr(ptr: NonNull<T>) -> Self {
        Self {
            ptr: Self::pointer_bits(ptr),
            marker: PhantomData,
        }
    }

    fn raw(&self) -> Option<NonNull<T>> {
        (self.ptr.get() != NULL_SENTINEL)
            .then(|| unsafe { NonNull::new_unchecked(self.ptr.get() as *mut T) })
    }

    pub fn from_shared(shared: &SharedIntrusive<T>) -> Self {
        let Some(ptr) = shared.raw() else {
            return Self::new();
        };
        unsafe { ptr.as_ref() }
            .intrusive_ref_counts()
            .add_weak_ref();
        Self::from_ptr(ptr)
    }

    pub fn assign_from_shared<Source>(&mut self, shared: &SharedIntrusive<Source>)
    where
        Source: IntrusiveStaticCast<T> + IntrusiveObject,
    {
        let next = shared.raw().map(Source::intrusive_static_cast);
        if let Some(raw) = next {
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_weak_ref();
        }
        self.release_and_store(next);
    }

    pub fn lock(&self) -> SharedIntrusive<T> {
        let Some(ptr) = self.raw() else {
            return SharedIntrusive::new();
        };
        if unsafe { ptr.as_ref() }
            .intrusive_ref_counts()
            .checkout_strong_ref_from_weak()
        {
            SharedIntrusive::from_ptr(ptr)
        } else {
            SharedIntrusive::new()
        }
    }

    pub fn expired(&self) -> bool {
        self.raw()
            .is_none_or(|ptr| unsafe { ptr.as_ref() }.intrusive_ref_counts().expired())
    }

    pub fn reset(&mut self) {
        self.release_and_store(None);
    }

    /// # Safety
    /// `ptr` must be null or point to a valid intrusive object whose refcount
    /// storage remains alive for this weak handle.
    pub unsafe fn adopt(&mut self, ptr: *mut T) {
        let next = NonNull::new(ptr);
        if let Some(raw) = next {
            assert_intrusive_alignment(raw);
            let object = unsafe { raw.as_ref() };
            let counts = object.intrusive_ref_counts();
            object.initialize_intrusive_owner(raw);
            counts.add_weak_ref();
        }
        self.release_and_store(next);
    }

    fn release_and_store(&mut self, next: Option<NonNull<T>>) {
        let previous = self.raw();
        self.ptr = next.map_or_else(null_handle, Self::pointer_bits);
        let Some(ptr) = previous else {
            return;
        };
        let counts = unsafe { ptr.as_ref() }.intrusive_ref_counts();
        if matches!(counts.release_weak_ref(), ReleaseWeakRefAction::Destroy) {
            unsafe { dispatch_final(ptr) };
        }
    }
}

impl<Target, Source> From<&SharedIntrusive<Source>> for WeakIntrusive<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject,
{
    fn from(value: &SharedIntrusive<Source>) -> Self {
        let Some(ptr) = value.raw().map(Source::intrusive_static_cast) else {
            return Self::new();
        };
        unsafe { ptr.as_ref() }
            .intrusive_ref_counts()
            .add_weak_ref();
        Self::from_ptr(ptr)
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

    pub const fn new() -> Self {
        Self {
            tagged_ptr: 0,
            marker: PhantomData,
        }
    }

    pub fn get_strong(&self) -> SharedIntrusive<T> {
        let Some(ptr) = self.raw() else {
            return SharedIntrusive::new();
        };
        if self.is_strong() {
            unsafe { ptr.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
            SharedIntrusive::from_ptr(ptr)
        } else {
            SharedIntrusive::new()
        }
    }

    pub fn reset(&mut self) {
        self.release_no_store();
        self.tagged_ptr = 0;
    }

    pub fn get(&self) -> Option<&T> {
        self.is_strong()
            .then(|| self.raw().map(|ptr| unsafe { ptr.as_ref() }))
            .flatten()
    }
    pub fn use_count(&self) -> usize {
        self.get()
            .map_or(0, |value| value.intrusive_ref_counts().use_count())
    }
    pub fn expired(&self) -> bool {
        self.raw()
            .is_none_or(|ptr| unsafe { ptr.as_ref() }.intrusive_ref_counts().expired())
    }

    pub fn lock(&self) -> SharedIntrusive<T> {
        let Some(ptr) = self.raw() else {
            return SharedIntrusive::new();
        };
        let counts = unsafe { ptr.as_ref() }.intrusive_ref_counts();
        if self.is_strong() {
            counts.add_strong_ref();
            return SharedIntrusive::from_ptr(ptr);
        }
        if counts.checkout_strong_ref_from_weak() {
            SharedIntrusive::from_ptr(ptr)
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
        let Some(ptr) = self.raw() else {
            return false;
        };
        let counts = unsafe { ptr.as_ref() }.intrusive_ref_counts();
        if counts.checkout_strong_ref_from_weak() {
            debug_assert_eq!(counts.release_weak_ref(), ReleaseWeakRefAction::Noop);
            self.set_raw(Some(ptr), RefStrength::Strong);
            true
        } else {
            false
        }
    }

    pub fn convert_to_weak(&mut self) -> bool {
        if self.is_weak() {
            return true;
        }
        let Some(ptr) = self.raw() else {
            return false;
        };
        let counts = unsafe { ptr.as_ref() }.intrusive_ref_counts();
        match counts.add_weak_release_strong_ref() {
            ReleaseStrongRefAction::Noop => {}
            ReleaseStrongRefAction::Destroy => {
                debug_assert!(false, "cannot destroy a freshly added weak ref");
                unsafe { dispatch_final(ptr) };
                self.tagged_ptr = 0;
                return true;
            }
            ReleaseStrongRefAction::PartialDestroy => unsafe { dispatch_partial(ptr) },
        }
        self.set_raw(Some(ptr), RefStrength::Weak);
        true
    }

    pub fn assign_from_shared<Source>(&mut self, shared: &SharedIntrusive<Source>)
    where
        Source: IntrusiveStaticCast<T> + IntrusiveObject,
    {
        let next = shared.raw().map(Source::intrusive_static_cast);
        if let Some(raw) = next {
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
        }
        self.release_no_store();
        self.set_raw(next, RefStrength::Strong);
    }

    pub fn assign_from_shared_owned<Source>(&mut self, shared: SharedIntrusive<Source>)
    where
        Source: IntrusiveStaticCast<T> + IntrusiveObject,
    {
        let shared = mem::ManuallyDrop::new(shared);
        let next = shared.raw().map(Source::intrusive_static_cast);
        self.release_no_store();
        self.set_raw(next, RefStrength::Strong);
    }

    fn raw(&self) -> Option<NonNull<T>> {
        NonNull::new((self.tagged_ptr & Self::PTR_MASK) as *mut T)
    }

    fn set_raw(&mut self, ptr: Option<NonNull<T>>, strength: RefStrength) {
        self.tagged_ptr = ptr.map_or(0, |raw| {
            assert_intrusive_alignment(raw);
            match strength {
                RefStrength::Strong => raw.as_ptr() as usize,
                RefStrength::Weak => raw.as_ptr() as usize | Self::TAG_MASK,
            }
        });
    }

    fn release_no_store(&mut self) {
        let Some(ptr) = self.raw() else {
            return;
        };
        let counts = unsafe { ptr.as_ref() }.intrusive_ref_counts();
        if self.is_strong() {
            match counts.release_strong_ref() {
                ReleaseStrongRefAction::Noop => {}
                ReleaseStrongRefAction::Destroy => unsafe { dispatch_final(ptr) },
                ReleaseStrongRefAction::PartialDestroy => unsafe { dispatch_partial(ptr) },
            }
        } else if matches!(counts.release_weak_ref(), ReleaseWeakRefAction::Destroy) {
            unsafe { dispatch_final(ptr) };
        }
    }
}

impl<T: IntrusiveObject> Clone for SharedWeakUnion<T> {
    fn clone(&self) -> Self {
        if let Some(raw) = self.raw() {
            let counts = unsafe { raw.as_ref() }.intrusive_ref_counts();
            if self.is_strong() {
                counts.add_strong_ref();
            } else {
                counts.add_weak_ref();
            }
        }
        Self {
            tagged_ptr: self.tagged_ptr,
            marker: PhantomData,
        }
    }
}
impl<T: IntrusiveObject> Drop for SharedWeakUnion<T> {
    fn drop(&mut self) {
        self.release_no_store();
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
    Target: IntrusiveObject,
{
    fn from(value: &SharedIntrusive<Source>) -> Self {
        let ptr = value.raw().map(Source::intrusive_static_cast);
        if let Some(raw) = ptr {
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_strong_ref();
        }
        let mut result = Self::new();
        result.set_raw(ptr, RefStrength::Strong);
        result
    }
}

impl<Target, Source> From<SharedIntrusive<Source>> for SharedWeakUnion<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject,
{
    fn from(value: SharedIntrusive<Source>) -> Self {
        let value = mem::ManuallyDrop::new(value);
        let mut result = Self::new();
        result.set_raw(
            value.raw().map(Source::intrusive_static_cast),
            RefStrength::Strong,
        );
        result
    }
}

impl<T: IntrusiveObject> From<&WeakIntrusive<T>> for SharedWeakUnion<T> {
    fn from(value: &WeakIntrusive<T>) -> Self {
        let ptr = value.raw();
        if let Some(raw) = ptr {
            unsafe { raw.as_ref() }
                .intrusive_ref_counts()
                .add_weak_ref();
        }
        let mut result = Self::new();
        result.set_raw(ptr, RefStrength::Weak);
        result
    }
}

impl<Target, Source> From<&SharedIntrusive<Source>> for SharedIntrusive<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject,
{
    fn from(value: &SharedIntrusive<Source>) -> Self {
        value.static_pointer_cast()
    }
}
impl<Target, Source> From<(StaticCastTagSharedIntrusive, &SharedIntrusive<Source>)>
    for SharedIntrusive<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject,
{
    fn from((_, value): (StaticCastTagSharedIntrusive, &SharedIntrusive<Source>)) -> Self {
        value.static_pointer_cast()
    }
}
impl<Target, Source> From<(StaticCastTagSharedIntrusive, SharedIntrusive<Source>)>
    for SharedIntrusive<Target>
where
    Source: IntrusiveStaticCast<Target> + IntrusiveObject,
    Target: IntrusiveObject,
{
    fn from((_, value): (StaticCastTagSharedIntrusive, SharedIntrusive<Source>)) -> Self {
        value.static_pointer_cast_owned()
    }
}
impl<Target, Source> From<(DynamicCastTagSharedIntrusive, &SharedIntrusive<Source>)>
    for SharedIntrusive<Target>
where
    Source: IntrusiveDynamicCast<Target> + IntrusiveObject,
    Target: IntrusiveObject,
{
    fn from((_, value): (DynamicCastTagSharedIntrusive, &SharedIntrusive<Source>)) -> Self {
        value.dynamic_pointer_cast()
    }
}
impl<Target, Source> TryFrom<(DynamicCastTagSharedIntrusive, SharedIntrusive<Source>)>
    for SharedIntrusive<Target>
where
    Source: IntrusiveDynamicCast<Target> + IntrusiveObject,
    Target: IntrusiveObject,
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
        if let Some(ptr) = self.raw() {
            unsafe { ptr.as_ref() }
                .intrusive_ref_counts()
                .add_weak_ref();
        }
        Self {
            ptr: self.ptr,
            marker: PhantomData,
        }
    }
}
impl<T: IntrusiveObject> Drop for WeakIntrusive<T> {
    fn drop(&mut self) {
        self.release_and_store(None);
    }
}
impl<T: IntrusiveObject> fmt::Debug for WeakIntrusive<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WeakIntrusive")
            .field("ptr", &self.raw())
            .field("expired", &self.expired())
            .finish()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RefStrength {
    Strong,
    Weak,
}

pub fn static_pointer_cast<Target, Source>(
    value: &SharedIntrusive<Source>,
) -> SharedIntrusive<Target>
where
    Source: IntrusiveStaticCast<Target>,
    Target: IntrusiveObject,
{
    value.static_pointer_cast()
}
pub fn dynamic_pointer_cast<Target, Source>(
    value: &SharedIntrusive<Source>,
) -> SharedIntrusive<Target>
where
    Source: IntrusiveDynamicCast<Target>,
    Target: IntrusiveObject,
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

    impl IntrusiveObject for TestNode {
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
