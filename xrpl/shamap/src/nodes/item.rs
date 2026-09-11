//! `xrpl/shamap/SHAMapItem.h` compatibility surface.

use basics::base_uint::Uint256;
use basics::blob::Blob;
use basics::byte_utilities::megabytes;
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};
use std::fmt;
use std::ptr::NonNull;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering, fence};

/// Header stored immediately before immutable SHAMap item payload bytes.
///
/// This deliberately matches rippled's 40-byte `SHAMapItem` object: 32-byte
/// key, 4-byte payload length, and 4-byte intrusive reference count.
#[repr(C)]
struct SHAMapItemHeader {
    key: Uint256,
    size: u32,
    ref_count: AtomicU32,
}

static ALLOCATED_ITEMS: AtomicU64 = AtomicU64::new(0);
static ALLOCATED_ITEM_BYTES: AtomicU64 = AtomicU64::new(0);

pub fn shamap_item_memory_stats() -> (u64, u64) {
    (
        ALLOCATED_ITEMS.load(Ordering::Relaxed),
        ALLOCATED_ITEM_BYTES.load(Ordering::Relaxed),
    )
}

const _: () = assert!(std::mem::size_of::<SHAMapItemHeader>() == 40);
const _: () = assert!(std::mem::align_of::<SHAMapItemHeader>() == 4);
pub const SHAMAP_ITEM_HEADER_SIZE: usize = std::mem::size_of::<SHAMapItemHeader>();
pub const SHAMAP_ITEM_HEADER_ALIGN: usize = std::mem::align_of::<SHAMapItemHeader>();

/// One-word owning handle to a rippled-layout SHAMap item allocation.
/// Payload bytes follow the 40-byte header in the same allocation.
pub struct SHAMapItem {
    header: NonNull<SHAMapItemHeader>,
}

const _: () = assert!(std::mem::size_of::<SHAMapItem>() == std::mem::size_of::<usize>());
const _: () = assert!(std::mem::align_of::<SHAMapItem>() == std::mem::align_of::<usize>());

// The header and payload are immutable after publication. The only mutable
// field is the atomic reference count.
unsafe impl Send for SHAMapItem {}
unsafe impl Sync for SHAMapItem {}

impl SHAMapItem {
    pub fn new(key: Uint256, data: impl Into<Blob>) -> Self {
        let data = data.into();
        assert!(
            data.len() <= megabytes::<usize>(16),
            "SHAMapItem data must not exceed 16 MB"
        );
        let size = u32::try_from(data.len()).expect("SHAMapItem length is bounded to 16 MiB");
        let layout = Self::layout(size as usize);
        let raw = unsafe { alloc(layout) };
        let header = NonNull::new(raw.cast::<SHAMapItemHeader>())
            .unwrap_or_else(|| handle_alloc_error(layout));
        unsafe {
            header.as_ptr().write(SHAMapItemHeader {
                key,
                size,
                ref_count: AtomicU32::new(1),
            });
            raw.add(std::mem::size_of::<SHAMapItemHeader>())
                .copy_from_nonoverlapping(data.as_ptr(), data.len());
        }
        ALLOCATED_ITEMS.fetch_add(1, Ordering::Relaxed);
        ALLOCATED_ITEM_BYTES.fetch_add(layout.size() as u64, Ordering::Relaxed);
        Self { header }
    }

    fn layout(payload_size: usize) -> Layout {
        Layout::from_size_align(
            std::mem::size_of::<SHAMapItemHeader>() + payload_size,
            std::mem::align_of::<SHAMapItemHeader>(),
        )
        .expect("bounded SHAMapItem layout")
    }

    fn header(&self) -> &SHAMapItemHeader {
        unsafe { self.header.as_ref() }
    }

    pub fn key(&self) -> Uint256 {
        self.header().key
    }

    pub fn size(&self) -> usize {
        self.header().size as usize
    }

    pub fn data(&self) -> &[u8] {
        unsafe {
            std::slice::from_raw_parts(
                self.header
                    .as_ptr()
                    .cast::<u8>()
                    .add(std::mem::size_of::<SHAMapItemHeader>()),
                self.size(),
            )
        }
    }

    #[cfg(test)]
    fn allocation_address(&self) -> usize {
        self.header.as_ptr() as usize
    }
}

impl Clone for SHAMapItem {
    fn clone(&self) -> Self {
        let previous = self.header().ref_count.fetch_add(1, Ordering::Relaxed);
        assert!(previous != 0, "cannot clone a released SHAMapItem");
        Self {
            header: self.header,
        }
    }
}

impl Drop for SHAMapItem {
    fn drop(&mut self) {
        if self.header().ref_count.fetch_sub(1, Ordering::Release) != 1 {
            return;
        }
        fence(Ordering::Acquire);
        let size = self.header().size as usize;
        let layout = Self::layout(size);
        ALLOCATED_ITEMS.fetch_sub(1, Ordering::Relaxed);
        ALLOCATED_ITEM_BYTES.fetch_sub(layout.size() as u64, Ordering::Relaxed);
        unsafe {
            std::ptr::drop_in_place(self.header.as_ptr());
            dealloc(self.header.as_ptr().cast::<u8>(), layout);
        }
    }
}

impl PartialEq for SHAMapItem {
    fn eq(&self, other: &Self) -> bool {
        self.key() == other.key() && self.data() == other.data()
    }
}

impl Eq for SHAMapItem {}

impl fmt::Debug for SHAMapItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SHAMapItem")
            .field("key", &self.key())
            .field("data", &self.data())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::{SHAMapItem, SHAMapItemHeader};
    use basics::base_uint::Uint256;

    #[test]
    fn layout_matches_rippled_inline_item_header() {
        assert_eq!(std::mem::size_of::<SHAMapItemHeader>(), 40);
        assert_eq!(std::mem::align_of::<SHAMapItemHeader>(), 4);
        assert_eq!(std::mem::size_of::<SHAMapItem>(), 8);
        assert_eq!(std::mem::align_of::<SHAMapItem>(), 8);
    }

    #[test]
    fn clone_shares_immutable_inline_payload() {
        let item = SHAMapItem::new(Uint256::from(7), vec![0xAB; 32]);
        let cloned = item.clone();
        assert_eq!(item.allocation_address(), cloned.allocation_address());
        assert_eq!(item, cloned);
        drop(item);
        assert_eq!(cloned.key(), Uint256::from(7));
        assert_eq!(cloned.data(), &[0xAB; 32]);
    }
}
