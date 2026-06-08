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
    fn missing_artifact_is_not_contained() {
        let tmp = tempfile::tempdir().unwrap();
        let store = Store::at(tmp.path());
        assert!(!store.contains(&content_address(b"absent")));
    }
}
