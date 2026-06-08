//! Content-addressed artifact store (pnpm's global store analogue).
//!
//! Artifacts are opaque byte blobs addressed by the lowercase hex
//! SHA-256 of their contents. The store is artifact-agnostic — it
//! neither knows nor cares that the bytes are WASM components — so
//! it is fully testable with synthetic bytes.
//!
//! Layout:
//! ```text
//! <root>/<sha256>/artifact.bin
//! ```
//! The default root is `$ADSMT_EMIT_STORE`, else
//! `$HOME/.adsmt/emit-store`, else `./.adsmt/emit-store`.

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

/// A content-addressed store rooted at a directory.
#[derive(Clone, Debug)]
pub struct Store {
    root: PathBuf,
}

/// Compute the lowercase-hex SHA-256 content address of `bytes`.
pub fn content_address(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    let digest = h.finalize();
    let mut s = String::with_capacity(64);
    for b in digest {
        use std::fmt::Write;
        let _ = write!(s, "{b:02x}");
    }
    s
}

impl Store {
    /// Open (do not create) a store at an explicit root.
    pub fn at(root: impl Into<PathBuf>) -> Self {
        Store { root: root.into() }
    }

    /// The default store root, honouring `$ADSMT_EMIT_STORE` then
    /// `$HOME/.adsmt/emit-store`.
    pub fn default_root() -> PathBuf {
        if let Some(explicit) = std::env::var_os("ADSMT_EMIT_STORE") {
            return PathBuf::from(explicit);
        }
        if let Some(home) = std::env::var_os("HOME") {
            return Path::new(&home).join(".adsmt").join("emit-store");
        }
        PathBuf::from(".adsmt").join("emit-store")
    }

    /// Open the store at [`Store::default_root`].
    pub fn open_default() -> Self {
        Store::at(Store::default_root())
    }

    /// The store root.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Directory holding the artifact for a given content address.
    pub fn dir_for(&self, sha256: &str) -> PathBuf {
        self.root.join(sha256)
    }

    /// Full path to the artifact for a given content address.
    pub fn path_for(&self, sha256: &str) -> PathBuf {
        self.dir_for(sha256).join("artifact.bin")
    }

    /// Whether an artifact with this content address is stored.
    pub fn contains(&self, sha256: &str) -> bool {
        self.path_for(sha256).is_file()
    }

    /// Add bytes to the store, returning their content address.
    /// Idempotent: storing identical bytes twice is a no-op on the
    /// second call.
    pub fn add(&self, bytes: &[u8]) -> std::io::Result<String> {
        let sha = content_address(bytes);
        let path = self.path_for(&sha);
        if !path.is_file() {
            std::fs::create_dir_all(self.dir_for(&sha))?;
            std::fs::write(&path, bytes)?;
        }
        Ok(sha)
    }

    /// Read a stored artifact by content address. Verifies the
    /// bytes still hash to the requested address (guards against a
    /// corrupted store).
    pub fn read(&self, sha256: &str) -> std::io::Result<Vec<u8>> {
        let bytes = std::fs::read(self.path_for(sha256))?;
        let actual = content_address(&bytes);
        if actual != sha256 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("store corruption: {sha256} hashes to {actual}"),
            ));
        }
        Ok(bytes)
    }

    /// Content-address an entire directory *tree* and store it
    /// unpacked under `<root>/<sha>/contents/`.
    ///
    /// The address is the SHA-256 of a canonical manifest: entries
    /// sorted by their forward-slash relative path, each
    /// contributing `relpath` + `NUL` + `len` (LE u64) + `bytes`.
    /// That is deterministic and platform-independent, so the same
    /// tree always yields the same address. Hashing is incremental
    /// (no whole-tree buffer). Idempotent.
    pub fn add_tree(&self, dir: &Path) -> std::io::Result<String> {
        let mut files = Vec::new();
        collect_files(dir, dir, &mut files)?;
        files.sort_by(|a, b| a.0.cmp(&b.0));

        let mut hasher = Sha256::new();
        for (rel, abs) in &files {
            let bytes = std::fs::read(abs)?;
            hasher.update(rel.as_bytes());
            hasher.update([0u8]);
            hasher.update((bytes.len() as u64).to_le_bytes());
            hasher.update(&bytes);
        }
        let mut sha = String::with_capacity(64);
        for b in hasher.finalize() {
            use std::fmt::Write;
            let _ = write!(sha, "{b:02x}");
        }

        let root = self.tree_root(&sha);
        if !root.is_dir() {
            for (rel, abs) in &files {
                let dest = root.join(rel);
                if let Some(parent) = dest.parent() {
                    std::fs::create_dir_all(parent)?;
                }
                std::fs::copy(abs, &dest)?;
            }
        }
        Ok(sha)
    }

    /// The `contents/` root of a stored tree.
    pub fn tree_root(&self, sha256: &str) -> PathBuf {
        self.dir_for(sha256).join("contents")
    }

    /// Path to a file within a stored tree, by tree-relative path.
    pub fn tree_path(&self, sha256: &str, rel: &Path) -> PathBuf {
        self.tree_root(sha256).join(rel)
    }

    /// Whether a tree with this content address is stored.
    pub fn contains_tree(&self, sha256: &str) -> bool {
        self.tree_root(sha256).is_dir()
    }
}

/// Recursively collect files under `dir` as
/// `(forward-slash relative path from root, absolute path)`,
/// visiting entries in a deterministic (name-sorted) order.
fn collect_files(
    root: &Path,
    dir: &Path,
    out: &mut Vec<(String, PathBuf)>,
) -> std::io::Result<()> {
    let mut entries: Vec<_> = std::fs::read_dir(dir)?.collect::<std::io::Result<Vec<_>>>()?;
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            collect_files(root, &path, out)?;
        } else {
            let rel = path.strip_prefix(root).unwrap_or(&path);
            let rel_str = rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("/");
            out.push((rel_str, path));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn content_address_is_stable_hex_sha256() {
        // SHA-256("") is the well-known empty-string digest.
        assert_eq!(
            content_address(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn add_read_roundtrip_and_idempotent() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        let sha = store.add(b"fake wasm bytes").unwrap();
        assert!(store.contains(&sha));
        assert_eq!(store.read(&sha).unwrap(), b"fake wasm bytes");
        // second add is a no-op, same address
        let sha2 = store.add(b"fake wasm bytes").unwrap();
        assert_eq!(sha, sha2);
    }

    #[test]
    fn add_tree_is_deterministic_and_readable() {
        let tmp = tempfile::tempdir().unwrap();
        let src = tmp.path().join("pkg");
        std::fs::create_dir_all(src.join("lib")).unwrap();
        std::fs::write(src.join("emitter.wasm"), b"\0asm\x01\0\0\0").unwrap();
        std::fs::write(src.join("lib/data.bin"), b"aux").unwrap();
        let store = Store::at(tmp.path().join("store"));

        let sha = store.add_tree(&src).unwrap();
        assert!(store.contains_tree(&sha));
        assert_eq!(
            std::fs::read(store.tree_path(&sha, std::path::Path::new("emitter.wasm"))).unwrap(),
            b"\0asm\x01\0\0\0"
        );
        assert_eq!(
            std::fs::read(store.tree_path(&sha, std::path::Path::new("lib/data.bin"))).unwrap(),
            b"aux"
        );
        // re-adding the identical tree is a no-op with the same address
        assert_eq!(store.add_tree(&src).unwrap(), sha);
    }

    #[test]
    fn add_tree_address_tracks_content() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path().join("store"));
        let a = tmp.path().join("a");
        let b = tmp.path().join("b");
        std::fs::create_dir_all(&a).unwrap();
        std::fs::create_dir_all(&b).unwrap();
        std::fs::write(a.join("x.wasm"), b"one").unwrap();
        std::fs::write(b.join("x.wasm"), b"two").unwrap();
        assert_ne!(store.add_tree(&a).unwrap(), store.add_tree(&b).unwrap());
    }

    #[test]
    fn missing_artifact_is_not_contained() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        assert!(!store.contains(&content_address(b"absent")));
    }
}
