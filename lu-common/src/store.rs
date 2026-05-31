use crate::hash::ContentSignature;
use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum StoreError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    #[error("corrupt store entry: {0}")]
    Corrupt(String),
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),
}

/// On-disk content store using **nested hash tables** for collision
/// resolution (Ticki, *Collision Resolution with Nested Hash Tables*).
///
/// At every level the slot for a key is `h_d(key) mod 256`, where `h_d` is
/// an FNV-1a-64 variant whose seed has been mixed with the depth so the
/// family `{h_0, h_1, ...}` is effectively independent. The disk image of
/// a node is a directory; each slot occupies *exactly one* of:
///
/// - `<slot>.json` — a leaf entry, or
/// - `<slot>/`     — a subtree (a deeper nested hash table).
///
/// Insertion at depth `d`:
///
/// - Empty slot → write leaf.
/// - Leaf with the same key → merge signatures.
/// - Leaf with a different key (a true collision) → delete the leaf,
///   create a subtree directory at the same slot, and recursively insert
///   *both* the old leaf and the new entry into it at depth `d + 1`.
/// - Existing subtree → descend and recurse.
///
/// Lookup walks the same chain. Most paths terminate at depth 0 (no
/// collisions). The expected lookup cost under good hash independence is
/// `O(log log N)`; the disk layout never grows wider than 256 slots per
/// node and never deeper than the longest collision chain.
///
/// Each leaf JSON has the same shape that earlier releases produced:
///
/// ```json
/// {
///   "path": "/absolute/path/to/file",
///   "signatures": {
///     "blake3": "abc123...",
///     "crc32": "deadbeef"
///   }
/// }
/// ```
pub struct ContentStore {
    root: PathBuf,
    /// Guards the one-shot migration from the v0.1 flat-fanout layout to
    /// the v0.2 nested-hashtable layout. `false` until the first
    /// successful `ensure_migrated()` call.
    migration_done: std::sync::Mutex<bool>,
}

/// Marker file written at the root of a v0.2 store. Its presence means
/// "this store has been migrated; skip the v0.1 sweep".
const FORMAT_MARKER: &str = ".format";
/// Body of the marker file.
const FORMAT_MARKER_VALUE: &str = "v2\n";

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct StoreEntry {
    path: String,
    signatures: HashMap<String, String>,
}

impl ContentStore {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self {
            root: root.into(),
            migration_done: std::sync::Mutex::new(false),
        }
    }

    pub fn default_path() -> PathBuf {
        PathBuf::from(".lu-store")
    }

    /// Record a content signature for a file. Merges with any existing
    /// signatures for the same path; resolves on-disk collisions by
    /// nesting deeper, never by overwriting another key's entry.
    pub fn record(&self, file_path: &Path, sig: &ContentSignature) -> Result<(), StoreError> {
        self.ensure_migrated()?;
        let key = file_path.to_string_lossy().into_owned();
        self.upsert(&key, |existing| {
            let mut entry = existing.unwrap_or_else(|| StoreEntry {
                path: key.clone(),
                signatures: HashMap::new(),
            });
            entry
                .signatures
                .insert(sig.method.clone(), sig.value.clone());
            entry
        })
    }

    /// Query stored signatures for a file.
    pub fn query(&self, file_path: &Path) -> Result<Option<Vec<ContentSignature>>, StoreError> {
        self.ensure_migrated()?;
        let key = file_path.to_string_lossy().into_owned();
        match self.lookup(&key)? {
            Some(entry) => {
                let sigs: Vec<ContentSignature> = entry
                    .signatures
                    .into_iter()
                    .map(|(method, value)| ContentSignature { method, value })
                    .collect();
                Ok(Some(sigs))
            }
            None => Ok(None),
        }
    }

    /// Check if a file's current signature differs from stored.
    pub fn differs(
        &self,
        file_path: &Path,
        current: &ContentSignature,
    ) -> Result<bool, StoreError> {
        self.ensure_migrated()?;
        let key = file_path.to_string_lossy().into_owned();
        match self.lookup(&key)? {
            Some(entry) => match entry.signatures.get(&current.method) {
                Some(stored_value) => Ok(stored_value != &current.value),
                None => Ok(true), // No stored value for this method
            },
            None => Ok(true), // No entry at all
        }
    }

    /// Remove entries for files that no longer exist on disk. Walks the
    /// nested-hashtable tree depth-first and prunes empty directories that
    /// remain after deletion.
    pub fn gc(&self) -> Result<u64, StoreError> {
        self.ensure_migrated()?;
        if !self.root.exists() {
            return Ok(0);
        }
        let mut removed = 0u64;
        Self::gc_node(&self.root, &mut removed)?;
        Ok(removed)
    }

    /// Run the v0.1 → v0.2 migration unconditionally and return the number
    /// of leaves migrated. Useful for explicit upgrade scripts.
    pub fn migrate_v1(&self) -> Result<u64, StoreError> {
        if !self.root.exists() {
            return Ok(0);
        }
        // Phase 1: collect every v0.1 leaf. Snapshot the listing first so
        // the subsequent inserts (which may write into the same `<NN>/`
        // directories we're scanning) can't perturb iteration.
        let mut v1_leaves: Vec<(PathBuf, StoreEntry)> = Vec::new();
        for entry in fs::read_dir(&self.root)? {
            let entry = entry?;
            if !entry.file_type()?.is_dir() {
                continue;
            }
            let name = entry.file_name();
            let dir_name = name.to_string_lossy();
            if !is_two_hex(&dir_name) {
                continue;
            }
            let dir_path = entry.path();
            for inner in fs::read_dir(&dir_path)? {
                let inner = inner?;
                if !inner.file_type()?.is_file() {
                    continue;
                }
                let inner_path = inner.path();
                if inner_path.extension().is_none_or(|e| e != "json") {
                    continue;
                }
                let stem = inner_path
                    .file_stem()
                    .map(|s| s.to_string_lossy().into_owned())
                    .unwrap_or_default();
                // v0.2 subtree leaves use a 2-hex-char basename; anything
                // else here is v0.1 (which used 14 hex chars after the
                // 2-hex bucket prefix).
                if is_two_hex(&stem) {
                    continue;
                }
                if let Some(leaf) = Self::load_leaf(&inner_path) {
                    v1_leaves.push((inner_path, leaf));
                }
            }
        }
        let count = v1_leaves.len() as u64;
        // Phase 2: re-insert each v0.1 leaf via the new addressing scheme,
        // then drop the old file. `insert_at` will route the entry to its
        // depth-0 (or deeper, on collision) slot under the v0.2 layout.
        for (old_path, entry) in v1_leaves {
            let key = entry.path.clone();
            self.insert_at(&self.root, &key, entry, 0)?;
            // Best-effort removal — already-vanished file is fine.
            let _ = fs::remove_file(&old_path);
        }
        // Phase 3: prune any 2-hex bucket directories that became empty
        // because their only contents were v0.1 leaves.
        for entry in fs::read_dir(&self.root)? {
            let entry = entry?;
            if !entry.file_type()?.is_dir() {
                continue;
            }
            let name = entry.file_name();
            if !is_two_hex(&name.to_string_lossy()) {
                continue;
            }
            let path = entry.path();
            if path
                .read_dir()
                .map(|mut it| it.next().is_none())
                .unwrap_or(false)
            {
                let _ = fs::remove_dir(&path);
            }
        }
        Ok(count)
    }

    /// First-touch guard: run `migrate_v1` exactly once per `ContentStore`
    /// instance, gated by an on-disk `.format` marker so subsequent
    /// processes also skip the sweep. Idempotent and concurrency-safe
    /// within a single process.
    fn ensure_migrated(&self) -> Result<(), StoreError> {
        let mut done = self.migration_done.lock().unwrap();
        if *done {
            return Ok(());
        }
        if !self.root.exists() {
            *done = true;
            return Ok(());
        }
        let marker = self.root.join(FORMAT_MARKER);
        if marker.is_file() {
            *done = true;
            return Ok(());
        }
        let migrated = self.migrate_v1()?;
        // Make sure the root still exists (it does, because migrate_v1
        // doesn't remove it) and stamp the marker so future invocations
        // skip the sweep.
        fs::create_dir_all(&self.root)?;
        fs::write(&marker, FORMAT_MARKER_VALUE)?;
        if migrated > 0 {
            eprintln!(
                "lu-store: migrated {migrated} entries from v0.1 (flat fanout) to v0.2 (nested hashtable) layout at {}",
                self.root.display()
            );
        }
        *done = true;
        Ok(())
    }

    fn gc_node(node_dir: &Path, removed: &mut u64) -> Result<(), StoreError> {
        for raw in fs::read_dir(node_dir)? {
            let raw = raw?;
            let name = raw.file_name();
            let name_str = name.to_string_lossy();
            // The format marker is metadata; never recurse into or remove it.
            if name_str == FORMAT_MARKER {
                continue;
            }
            let path = raw.path();
            let ft = raw.file_type()?;
            if ft.is_dir() {
                // Only descend into proper slot directories. Anything else
                // (e.g. user-created dotfiles) is left untouched.
                if !is_two_hex(&name_str) {
                    continue;
                }
                Self::gc_node(&path, removed)?;
                // Prune subtree directories that are now empty.
                if path.read_dir().map(|mut it| it.next().is_none()).unwrap_or(false) {
                    let _ = fs::remove_dir(&path);
                }
            } else if ft.is_file() && path.extension().is_some_and(|e| e == "json") {
                if let Some(entry) = Self::load_leaf(&path) {
                    if !Path::new(&entry.path).exists() {
                        fs::remove_file(&path)?;
                        *removed += 1;
                    }
                }
            }
        }
        Ok(())
    }

    /// Walk down the tree to the slot owning `key` and apply `f` to the
    /// existing entry (if any). Handles collision splitting.
    fn upsert<F>(&self, key: &str, f: F) -> Result<(), StoreError>
    where
        F: FnOnce(Option<StoreEntry>) -> StoreEntry,
    {
        fs::create_dir_all(&self.root)?;
        let existing = self.lookup(key)?;
        let entry = f(existing);
        self.insert_at(&self.root, key, entry, 0)
    }

    fn insert_at(
        &self,
        node_dir: &Path,
        key: &str,
        entry: StoreEntry,
        depth: u32,
    ) -> Result<(), StoreError> {
        fs::create_dir_all(node_dir)?;
        let slot = level_hash(key, depth);
        let leaf_path = node_dir.join(slot_leaf_name(slot));
        let sub_path = node_dir.join(slot_dir_name(slot));

        if sub_path.is_dir() {
            // Existing subtree at this slot — recurse deeper.
            return self.insert_at(&sub_path, key, entry, depth + 1);
        }

        if leaf_path.is_file() {
            if let Some(existing) = Self::load_leaf(&leaf_path) {
                if existing.path == key {
                    // Same key — merge.
                    Self::write_leaf(&leaf_path, &entry)?;
                    return Ok(());
                }
                // True collision: replace the leaf with a subtree and
                // re-insert *both* entries one level deeper. The hash
                // function at depth+1 is independent of the one used
                // here, so the two keys almost certainly land in
                // different slots (otherwise we recurse again).
                fs::remove_file(&leaf_path)?;
                fs::create_dir(&sub_path)?;
                self.insert_at(&sub_path, &existing.path.clone(), existing, depth + 1)?;
                return self.insert_at(&sub_path, key, entry, depth + 1);
            }
            // Unreadable leaf: overwrite it; safer than leaving corrupt JSON.
        }

        Self::write_leaf(&leaf_path, &entry)
    }

    fn lookup(&self, key: &str) -> Result<Option<StoreEntry>, StoreError> {
        if !self.root.exists() {
            return Ok(None);
        }
        let mut node_dir = self.root.clone();
        let mut depth = 0u32;
        loop {
            let slot = level_hash(key, depth);
            let leaf_path = node_dir.join(slot_leaf_name(slot));
            let sub_path = node_dir.join(slot_dir_name(slot));
            if sub_path.is_dir() {
                node_dir = sub_path;
                depth += 1;
                // Hard cap matches the maximum number of independent hash
                // functions we generate; with 256-way fanout per level, the
                // probability of needing >32 levels for any realistic
                // workload is astronomical.
                if depth > 32 {
                    return Ok(None);
                }
                continue;
            }
            if leaf_path.is_file() {
                if let Some(entry) = Self::load_leaf(&leaf_path) {
                    if entry.path == key {
                        return Ok(Some(entry));
                    }
                }
            }
            return Ok(None);
        }
    }

    fn load_leaf(entry_path: &Path) -> Option<StoreEntry> {
        let data = fs::read_to_string(entry_path).ok()?;
        serde_json::from_str(&data).ok()
    }

    fn write_leaf(entry_path: &Path, entry: &StoreEntry) -> Result<(), StoreError> {
        let data = serde_json::to_string_pretty(entry)?;
        // Atomic-on-Unix write via tempfile + rename.
        let tmp = entry_path.with_extension("json.tmp");
        fs::write(&tmp, data)?;
        fs::rename(&tmp, entry_path)?;
        Ok(())
    }
}

/// Format a slot's leaf file name (`"NN.json"`).
fn slot_leaf_name(slot: u8) -> String {
    format!("{slot:02x}.json")
}

/// True iff `s` is exactly two ASCII hex digits — the form used for
/// every slot name (leaf stem or subtree directory) in the v0.2 layout.
fn is_two_hex(s: &str) -> bool {
    s.len() == 2 && s.chars().all(|c| c.is_ascii_hexdigit())
}

/// Format a slot's subtree directory name (`"NN"`).
fn slot_dir_name(slot: u8) -> String {
    format!("{slot:02x}")
}

/// Hash family used for nested-hashtable slot selection.
///
/// `h_d(key) = FNV-1a-64(key)` started from a depth-mixed seed. Different
/// depths therefore use *different, effectively independent* hash
/// functions — the property Ticki's analysis relies on. The result is
/// reduced to a single byte, giving 256-way fanout per level.
fn level_hash(s: &str, depth: u32) -> u8 {
    // Mix the depth into the FNV seed via Knuth's golden-ratio constant so
    // depth 0, 1, 2... produce uncorrelated initial states.
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const GOLDEN: u64 = 0x9e3779b97f4a7c15;
    let mut h = FNV_OFFSET ^ (depth as u64).wrapping_mul(GOLDEN);
    for byte in s.as_bytes() {
        h ^= *byte as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    (h & 0xff) as u8
}

/// Backwards-compatible flat hash, retained only for the public API of
/// older releases that exposed it. Internal logic uses `level_hash`.
#[doc(hidden)]
pub fn simple_path_hash(s: &str) -> String {
    let mut hash: u64 = 0xcbf29ce484222325;
    for byte in s.as_bytes() {
        hash ^= *byte as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("{hash:016x}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_store_record_query() {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));

        let file_path = Path::new("/tmp/test-file.txt");
        let sig = ContentSignature {
            method: "blake3".into(),
            value: "abc123def456".into(),
        };

        store.record(file_path, &sig).unwrap();

        let result = store.query(file_path).unwrap().unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].method, "blake3");
        assert_eq!(result[0].value, "abc123def456");
    }

    #[test]
    fn test_store_differs() {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));
        let file_path = Path::new("/tmp/test-file.txt");

        let sig1 = ContentSignature {
            method: "blake3".into(),
            value: "abc123".into(),
        };
        store.record(file_path, &sig1).unwrap();

        // Same value -> not different
        assert!(!store.differs(file_path, &sig1).unwrap());

        // Different value -> different
        let sig2 = ContentSignature {
            method: "blake3".into(),
            value: "xyz789".into(),
        };
        assert!(store.differs(file_path, &sig2).unwrap());
    }

    #[test]
    fn test_store_query_nonexistent() {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));
        let result = store.query(Path::new("/no/such/file")).unwrap();
        assert!(result.is_none());
    }

    #[test]
    fn test_gc() {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));

        // Create a real file, record it, then delete it
        let real_file = dir.path().join("real.txt");
        fs::write(&real_file, "content").unwrap();
        let sig = ContentSignature {
            method: "crc32".into(),
            value: "deadbeef".into(),
        };
        store.record(&real_file, &sig).unwrap();
        fs::remove_file(&real_file).unwrap();

        let removed = store.gc().unwrap();
        assert_eq!(removed, 1);

        // Entry should be gone
        assert!(store.query(&real_file).unwrap().is_none());
    }

    #[test]
    fn test_simple_path_hash_deterministic() {
        let h1 = simple_path_hash("/foo/bar.txt");
        let h2 = simple_path_hash("/foo/bar.txt");
        assert_eq!(h1, h2);
        assert_eq!(h1.len(), 16);
    }

    #[test]
    fn test_simple_path_hash_distribution() {
        let h1 = simple_path_hash("/foo/bar.txt");
        let h2 = simple_path_hash("/foo/baz.txt");
        assert_ne!(h1, h2);
    }

    /// Helper: brute-force a string that collides with `target_key` at the
    /// given depth using `level_hash`. Returns the colliding key.
    fn find_colliding_key(target_key: &str, depth: u32) -> String {
        let target = level_hash(target_key, depth);
        for i in 0..1_000_000u64 {
            let candidate = format!("/collide-probe-{i}");
            if candidate != target_key && level_hash(&candidate, depth) == target {
                return candidate;
            }
        }
        panic!("could not find collision for {target_key} at depth {depth}");
    }

    #[test]
    fn test_collision_triggers_nesting() {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));

        let key_a = String::from("/path/A");
        let key_b = find_colliding_key(&key_a, 0);
        assert_eq!(level_hash(&key_a, 0), level_hash(&key_b, 0));
        assert_ne!(key_a, key_b);

        let sig_a = ContentSignature { method: "blake3".into(), value: "AAA".into() };
        let sig_b = ContentSignature { method: "blake3".into(), value: "BBB".into() };

        // First insert: should land as a leaf at depth 0.
        store.record(Path::new(&key_a), &sig_a).unwrap();
        let slot = level_hash(&key_a, 0);
        let leaf0 = dir.path().join(".lu-store").join(format!("{slot:02x}.json"));
        let sub0 = dir.path().join(".lu-store").join(format!("{slot:02x}"));
        assert!(leaf0.is_file(), "first insert should be a depth-0 leaf");
        assert!(!sub0.is_dir(), "no subtree yet");

        // Second insert: collision with key_a → leaf at slot must become
        // a subtree containing two leaves at depth 1.
        store.record(Path::new(&key_b), &sig_b).unwrap();
        assert!(!leaf0.is_file(), "leaf at root slot must be replaced");
        assert!(sub0.is_dir(), "subtree must be created at the colliding slot");

        // Each colliding key now lives at a depth-1 slot inside the subtree.
        let sub_a = level_hash(&key_a, 1);
        let sub_b = level_hash(&key_b, 1);
        // If the two collide again at depth 1 (~1/256 chance), the test
        // would still be valid — we just check that both keys retrieve.
        if sub_a != sub_b {
            assert!(sub0.join(format!("{sub_a:02x}.json")).is_file());
            assert!(sub0.join(format!("{sub_b:02x}.json")).is_file());
        }

        // Both queries must return the correct, distinct entries.
        let got_a = store.query(Path::new(&key_a)).unwrap().unwrap();
        let got_b = store.query(Path::new(&key_b)).unwrap().unwrap();
        assert_eq!(got_a.len(), 1);
        assert_eq!(got_a[0].value, "AAA");
        assert_eq!(got_b.len(), 1);
        assert_eq!(got_b[0].value, "BBB");
    }

    #[test]
    fn test_collision_does_not_overwrite() {
        // Regression test for the old flat fanout that silently clobbered
        // collisions: insert two distinct paths whose depth-0 hashes
        // collide, then verify that *both* survive.
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));

        let key_a = String::from("/data/sample.fastq");
        let key_b = find_colliding_key(&key_a, 0);
        let sig_a = ContentSignature { method: "blake3".into(), value: "AAA".into() };
        let sig_b = ContentSignature { method: "blake3".into(), value: "BBB".into() };

        store.record(Path::new(&key_a), &sig_a).unwrap();
        store.record(Path::new(&key_b), &sig_b).unwrap();

        let got_a = store.query(Path::new(&key_a)).unwrap().unwrap();
        let got_b = store.query(Path::new(&key_b)).unwrap().unwrap();
        assert_eq!(got_a[0].value, "AAA");
        assert_eq!(got_b[0].value, "BBB");
    }

    #[test]
    fn test_three_way_collision_at_depth_zero() {
        // Force three keys all colliding at depth 0; the tree must split
        // recursively as needed.
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));

        let key_a = String::from("/triple/a");
        let key_b = find_colliding_key(&key_a, 0);
        // Find a third key colliding with key_a at depth 0 but distinct
        // from key_b.
        let target = level_hash(&key_a, 0);
        let mut key_c = String::new();
        for i in 0..2_000_000u64 {
            let candidate = format!("/triple-probe-{i}");
            if candidate != key_a
                && candidate != key_b
                && level_hash(&candidate, 0) == target
            {
                key_c = candidate;
                break;
            }
        }
        assert!(!key_c.is_empty());

        store
            .record(Path::new(&key_a), &ContentSignature { method: "x".into(), value: "1".into() })
            .unwrap();
        store
            .record(Path::new(&key_b), &ContentSignature { method: "x".into(), value: "2".into() })
            .unwrap();
        store
            .record(Path::new(&key_c), &ContentSignature { method: "x".into(), value: "3".into() })
            .unwrap();

        for (k, want) in [(&key_a, "1"), (&key_b, "2"), (&key_c, "3")] {
            let got = store.query(Path::new(k)).unwrap().unwrap();
            assert_eq!(got[0].value, want, "key {k} should resolve to {want}");
        }
    }

    #[test]
    fn test_no_collision_stays_at_depth_zero() {
        // Sanity: typical path inserts must not pay for nested addressing.
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));
        let p = Path::new("/no/collision/here");
        store
            .record(p, &ContentSignature { method: "blake3".into(), value: "ok".into() })
            .unwrap();
        let slot = level_hash(&p.to_string_lossy(), 0);
        let leaf = dir.path().join(".lu-store").join(format!("{slot:02x}.json"));
        assert!(leaf.is_file(), "uncontested insert must stay at depth 0");
    }

    #[test]
    fn test_gc_prunes_empty_subtrees() {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));

        let real = dir.path().join("real.txt");
        fs::write(&real, "x").unwrap();
        let collide = find_colliding_key(&real.to_string_lossy(), 0);

        store
            .record(&real, &ContentSignature { method: "x".into(), value: "1".into() })
            .unwrap();
        // Force a real collision so a subtree exists.
        store
            .record(Path::new(&collide), &ContentSignature { method: "x".into(), value: "2".into() })
            .unwrap();

        // Both files don't exist on disk — only `real` does. After deleting
        // `real`, gc must remove both leaves and prune the subtree.
        fs::remove_file(&real).unwrap();
        let removed = store.gc().unwrap();
        assert_eq!(removed, 2, "gc should remove both leaves");
        // Empty subtree directory should have been pruned.
        let slot = level_hash(&real.to_string_lossy(), 0);
        let sub = dir.path().join(".lu-store").join(format!("{slot:02x}"));
        assert!(!sub.exists(), "empty subtree directory should be pruned");
    }

    /// Reconstruct the v0.1 layout directly: hash the path with FNV-1a-64,
    /// take the first byte as the bucket directory, and the remaining 14
    /// hex chars as the leaf filename.
    fn write_v1_leaf(root: &Path, key: &str, sigs: &[(&str, &str)]) {
        let h = simple_path_hash(key);
        let bucket = &h[..2];
        let rest = &h[2..];
        let dir = root.join(bucket);
        fs::create_dir_all(&dir).unwrap();
        let mut sig_map: HashMap<String, String> = HashMap::new();
        for (m, v) in sigs {
            sig_map.insert((*m).into(), (*v).into());
        }
        let entry = StoreEntry {
            path: key.into(),
            signatures: sig_map,
        };
        fs::write(
            dir.join(format!("{rest}.json")),
            serde_json::to_string_pretty(&entry).unwrap(),
        )
        .unwrap();
    }

    #[test]
    fn test_auto_migration_lookup_recovers_v1_entries() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join(".lu-store");
        fs::create_dir_all(&root).unwrap();
        // No `.format` marker → v0.1 layout assumed.
        write_v1_leaf(&root, "/legacy/A", &[("blake3", "AAA")]);
        write_v1_leaf(&root, "/legacy/B", &[("blake3", "BBB")]);

        // First contact: lookup must auto-migrate and return the entry.
        let store = ContentStore::new(&root);
        let got_a = store.query(Path::new("/legacy/A")).unwrap().unwrap();
        let got_b = store.query(Path::new("/legacy/B")).unwrap().unwrap();
        assert_eq!(got_a[0].value, "AAA");
        assert_eq!(got_b[0].value, "BBB");
        // Marker must be present afterwards.
        assert!(root.join(FORMAT_MARKER).is_file());

        // The legacy bucket directories must be either gone or contain
        // only valid v0.2 leaves (2-hex stems).
        for ent in fs::read_dir(&root).unwrap() {
            let ent = ent.unwrap();
            let name = ent.file_name().to_string_lossy().into_owned();
            if name == FORMAT_MARKER || !ent.file_type().unwrap().is_dir() {
                continue;
            }
            for inner in fs::read_dir(ent.path()).unwrap() {
                let inner = inner.unwrap();
                let stem = inner
                    .path()
                    .file_stem()
                    .map(|s| s.to_string_lossy().into_owned())
                    .unwrap_or_default();
                assert!(
                    is_two_hex(&stem),
                    "leftover non-v0.2 leaf after migration: {stem}"
                );
            }
        }
    }

    #[test]
    fn test_auto_migration_idempotent() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join(".lu-store");
        fs::create_dir_all(&root).unwrap();
        write_v1_leaf(&root, "/idem/A", &[("crc32", "feedface")]);

        let store = ContentStore::new(&root);
        store.query(Path::new("/idem/A")).unwrap();
        // Second store on the same root: marker is present, migrate should
        // no-op. We verify by counting that nothing changes.
        let store2 = ContentStore::new(&root);
        let migrated = store2.migrate_v1().unwrap();
        assert_eq!(migrated, 0, "second migration must find no v0.1 entries");
        // Querying still works.
        assert_eq!(
            store2
                .query(Path::new("/idem/A"))
                .unwrap()
                .unwrap()[0]
                .value,
            "feedface"
        );
    }

    #[test]
    fn test_migration_preserves_collisions() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join(".lu-store");
        fs::create_dir_all(&root).unwrap();
        // Two v0.1 entries that, in the v0.2 family, collide at depth 0.
        // After migration they must coexist as a subtree, not lose data.
        let key_a = "/migrate/collision-A".to_string();
        let key_b = find_colliding_key(&key_a, 0);
        write_v1_leaf(&root, &key_a, &[("x", "AAA")]);
        write_v1_leaf(&root, &key_b, &[("x", "BBB")]);

        let store = ContentStore::new(&root);
        let got_a = store.query(Path::new(&key_a)).unwrap().unwrap();
        let got_b = store.query(Path::new(&key_b)).unwrap().unwrap();
        assert_eq!(got_a[0].value, "AAA");
        assert_eq!(got_b[0].value, "BBB");
        // The colliding slot must have become a subtree.
        let slot = level_hash(&key_a, 0);
        let sub = root.join(format!("{slot:02x}"));
        assert!(sub.is_dir(), "v0.2 subtree must hold both entries");
    }

    #[test]
    fn test_migration_coexists_with_v2_entries() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join(".lu-store");
        fs::create_dir_all(&root).unwrap();

        // Pre-existing v0.2 leaves: write through ContentStore (which
        // stamps the marker as a side effect) — but we want a *mixed*
        // store, so write the v0.2 leaf manually and then drop a v0.1
        // leaf into the same hex bucket.
        let v2_key = "/v2-only/file".to_string();
        let v2_slot = level_hash(&v2_key, 0);
        // Place the v0.2 leaf at slot v2_slot, depth 0.
        let v2_entry = StoreEntry {
            path: v2_key.clone(),
            signatures: [("x".to_string(), "V2".to_string())].into_iter().collect(),
        };
        fs::write(
            root.join(format!("{v2_slot:02x}.json")),
            serde_json::to_string_pretty(&v2_entry).unwrap(),
        )
        .unwrap();

        // v0.1 leaf inside a 2-hex directory (the bucket form) — distinct
        // from v2_slot's bucket so paths can coexist.
        let v1_key = "/v1-only/file".to_string();
        write_v1_leaf(&root, &v1_key, &[("x", "V1")]);

        // No marker: trigger migration via lookup.
        let store = ContentStore::new(&root);
        // Both must remain queryable.
        assert_eq!(store.query(Path::new(&v2_key)).unwrap().unwrap()[0].value, "V2");
        assert_eq!(store.query(Path::new(&v1_key)).unwrap().unwrap()[0].value, "V1");
    }

    #[test]
    fn test_level_hash_independence_per_depth() {
        // The whole point of "different hash functions per depth" is that
        // a depth-0 collision rarely also collides at depth 1. Verify that
        // for a sample of forced depth-0 collisions, the depth-1 hashes
        // are *not* perfectly correlated.
        let key_a = "/independence/probe";
        let target0 = level_hash(key_a, 0);
        let mut both_collide = 0usize;
        let mut sample = 0usize;
        for i in 0..10_000u64 {
            let cand = format!("/independence-{i}");
            if level_hash(&cand, 0) == target0 {
                sample += 1;
                if level_hash(&cand, 1) == level_hash(key_a, 1) {
                    both_collide += 1;
                }
            }
        }
        // With independent hashes we expect ~sample/256 secondary collisions,
        // i.e. a small fraction. If depth-1 were the same function as
        // depth-0 we would get sample/sample == 100%. Anything above
        // ~25% would indicate a broken family.
        if sample > 0 {
            assert!(
                both_collide as f64 / sample as f64 <= 0.25,
                "depth-1 hash should be largely independent of depth-0 (got {}/{} = {:.2}%)",
                both_collide,
                sample,
                100.0 * both_collide as f64 / sample as f64
            );
        }
    }
}
