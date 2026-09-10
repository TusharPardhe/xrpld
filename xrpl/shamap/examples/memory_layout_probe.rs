use basics::base_uint::Uint256;
use basics::intrusive_pointer::{SharedIntrusive, SharedWeakUnion, WeakIntrusive};
use shamap::item::{SHAMAP_ITEM_HEADER_ALIGN, SHAMAP_ITEM_HEADER_SIZE, SHAMapItem};
use shamap::tree_node::{SHAMapInnerNode, SHAMapLeafNode, SHAMapTreeNode};
use std::mem::{align_of, size_of};
fn p<T>(n: &str) {
    println!("{n}: size={} align={}", size_of::<T>(), align_of::<T>());
}
fn main() {
    p::<SHAMapTreeNode>("SHAMapTreeNode");
    p::<SHAMapInnerNode>("SHAMapInnerNode allocation");
    p::<SHAMapLeafNode>("SHAMapLeafNode allocation");
    println!(
        "SHAMapItem allocation header: size={} align={}",
        SHAMAP_ITEM_HEADER_SIZE, SHAMAP_ITEM_HEADER_ALIGN
    );
    p::<SHAMapItem>("SHAMapItem handle");
    p::<SharedIntrusive<SHAMapTreeNode>>("SharedIntrusive");
    p::<WeakIntrusive<SHAMapTreeNode>>("WeakIntrusive");
    p::<SharedWeakUnion<SHAMapTreeNode>>("SharedWeakUnion");
    p::<Uint256>("Uint256");
    p::<Option<SharedIntrusive<SHAMapTreeNode>>>("OptionSharedIntrusive");
}
