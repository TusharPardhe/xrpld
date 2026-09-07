//! Disk-backed import of public `ledger_data` leaves into verified SHAMap nodes.

use basics::base_uint::Uint256;
use serde_json::Value;
use shamap::{
    item::SHAMapItem,
    mutation::MutableTree,
    tree_node::{SHAMapNodeType, SHAMapTreeNode},
};
use std::fs::{self, File};
use std::io::{BufRead, BufReader};
use std::path::Path;

const FLUSH_EVERY: u64 = 1_024;

fn node_path(nodes: &Path, hash: &str) -> std::path::PathBuf {
    nodes.join(&hash[..2]).join(format!("{hash}.node"))
}

fn store_node(nodes: &Path, node: &SHAMapTreeNode) -> Result<(), String> {
    let hash = node.get_hash().to_string();
    let path = node_path(nodes, &hash);
    if path.exists() {
        return Ok(());
    }
    let parent = path
        .parent()
        .ok_or_else(|| "node object path has no parent".to_owned())?;
    fs::create_dir_all(parent).map_err(|error| format!("create {}: {error}", parent.display()))?;
    let raw = node
        .serialize_for_wire()
        .map_err(|error| format!("serialize SHAMap node {hash}: {error:?}"))?;
    fs::write(&path, raw).map_err(|error| format!("write {}: {error}", path.display()))
}

fn load_node(
    nodes: &Path,
    hash: &str,
) -> Option<basics::intrusive_pointer::SharedIntrusive<SHAMapTreeNode>> {
    let raw = fs::read(node_path(nodes, hash)).ok()?;
    SHAMapTreeNode::make_from_wire(&raw).ok().flatten()
}

fn parse_leaf(line: &str, number: u64) -> Result<(Uint256, Vec<u8>), String> {
    let row: Value = serde_json::from_str(line)
        .map_err(|error| format!("parse parent-state.jsonl line {number}: {error}"))?;
    let index = row["index"]
        .as_str()
        .ok_or_else(|| format!("parent-state.jsonl line {number} omitted index"))?;
    let data = row["data"]
        .as_str()
        .ok_or_else(|| format!("parent-state.jsonl line {number} omitted binary data"))?;
    let key = Uint256::from_hex(index)
        .map_err(|error| format!("parent-state.jsonl line {number} invalid index: {error:?}"))?;
    let bytes = hex::decode(data)
        .map_err(|error| format!("parent-state.jsonl line {number} invalid data: {error}"))?;
    Ok((key, bytes))
}

/// Import a parent snapshot to a content-addressed, disk-backed SHAMap store.
///
/// Each flush replaces loaded descendants with wire-decoded hash links. Later
/// insertions fetch only the path they need from `nodes/`, keeping memory
/// bounded instead of retaining a full account tree in RAM.
pub fn import_parent(fixture: &Path) -> Result<(String, u64), String> {
    let source = fixture.join("parent-state.jsonl");
    let nodes = fixture.join("parent-nodestore");
    if nodes.exists() {
        return Err(format!(
            "refusing to overwrite existing disk-backed import {}",
            nodes.display()
        ));
    }
    fs::create_dir_all(&nodes).map_err(|error| format!("create {}: {error}", nodes.display()))?;
    let file =
        File::open(&source).map_err(|error| format!("open {}: {error}", source.display()))?;
    let mut tree = MutableTree::new(1);
    let mut imported = 0_u64;
    for (offset, line) in BufReader::new(file).lines().enumerate() {
        let number = offset as u64 + 1;
        let line =
            line.map_err(|error| format!("read {} line {number}: {error}", source.display()))?;
        let (key, data) = parse_leaf(&line, number)?;
        let mut fetch =
            |hash: basics::sha_map_hash::SHAMapHash| load_node(&nodes, &hash.to_string());
        tree.add_item_with_fetch(
            SHAMapNodeType::AccountState,
            SHAMapItem::new(key, data),
            &mut fetch,
        )
        .map_err(|error| format!("insert parent state leaf {number}: {error:?}"))?;
        imported += 1;
        if imported.is_multiple_of(FLUSH_EVERY) {
            tree.try_flush_dirty(&mut |node| {
                store_node(&nodes, &node)?;
                let raw = node
                    .serialize_for_wire()
                    .map_err(|error| format!("{error:?}"))?;
                SHAMapTreeNode::make_from_wire(&raw)
                    .map_err(|error| format!("{error:?}"))?
                    .ok_or_else(|| "SHAMap node codec returned no node".to_owned())
            })
            .map_err(|error: String| error)?;
        }
    }
    tree.try_flush_dirty(&mut |node| {
        store_node(&nodes, &node)?;
        let raw = node
            .serialize_for_wire()
            .map_err(|error| format!("{error:?}"))?;
        SHAMapTreeNode::make_from_wire(&raw)
            .map_err(|error| format!("{error:?}"))?
            .ok_or_else(|| "SHAMap node codec returned no node".to_owned())
    })
    .map_err(|error: String| error)?;
    Ok((tree.root().get_hash().to_string(), imported))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn disk_backed_import_preserves_the_shamap_root() {
        let fixture = std::env::temp_dir().join(format!(
            "quaxar-ledger-audit-{}",
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("clock after epoch")
                .as_nanos()
        ));
        fs::create_dir_all(&fixture).expect("create fixture directory");
        let leaves = [
            (
                "1000000000000000000000000000000000000000000000000000000000000000",
                vec![0x11; 16],
            ),
            (
                "A000000000000000000000000000000000000000000000000000000000000000",
                vec![0x22; 16],
            ),
            (
                "F000000000000000000000000000000000000000000000000000000000000000",
                vec![0x33; 16],
            ),
        ];
        let mut expected = MutableTree::new(1);
        let mut jsonl = String::new();
        for (key, data) in &leaves {
            expected
                .add_item(
                    SHAMapNodeType::AccountState,
                    SHAMapItem::new(Uint256::from_hex(key).expect("valid key"), data.clone()),
                )
                .expect("insert expected leaf");
            jsonl.push_str(
                &serde_json::json!({"index": key, "data": hex::encode(data)}).to_string(),
            );
            jsonl.push('\n');
        }
        fs::write(fixture.join("parent-state.jsonl"), jsonl).expect("write state");

        expected.unshare();
        let (actual, count) = import_parent(&fixture).expect("import fixture");
        assert_eq!(count, leaves.len() as u64);
        assert_eq!(actual, expected.root().get_hash().to_string());
        assert!(fixture.join("parent-nodestore").exists());
        fs::remove_dir_all(fixture).expect("remove fixture");
    }
}
