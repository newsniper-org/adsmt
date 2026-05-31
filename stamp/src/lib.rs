use lu_common::format::{FormatWriter, Record};
use lu_common::hash::{self, ContentSignature, FreshnessMethod, HashError};
use lu_common::store::{ContentStore, StoreError};
use std::fs::{self, File};
use std::io;
use std::path::Path;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum StampError {
    #[error("{0}")]
    Hash(#[from] HashError),
    #[error("{0}")]
    Store(#[from] StoreError),
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    #[error("file not found: {0}")]
    FileNotFound(String),
    #[error("{0}")]
    Format(#[from] lu_common::format::FormatError),
}

/// Compute content signature(s) for a file using the given method.
pub fn compute_signature(path: &Path, method: FreshnessMethod) -> Result<ContentSignature, StampError> {
    match method {
        FreshnessMethod::Hash(algo) => {
            let mut file = File::open(path)
                .map_err(|_| StampError::FileNotFound(path.display().to_string()))?;
            Ok(hash::hash_reader(algo, &mut file)?)
        }
        FreshnessMethod::Checksum(algo) => {
            let mut file = File::open(path)
                .map_err(|_| StampError::FileNotFound(path.display().to_string()))?;
            Ok(hash::checksum_reader(algo, &mut file)?)
        }
        FreshnessMethod::Size => {
            let meta = fs::metadata(path)
                .map_err(|_| StampError::FileNotFound(path.display().to_string()))?;
            Ok(hash::size_signature(meta.len()))
        }
        FreshnessMethod::Timestamp | FreshnessMethod::Always => {
            // Timestamp and Always don't produce content signatures
            let meta = fs::metadata(path)
                .map_err(|_| StampError::FileNotFound(path.display().to_string()))?;
            let modified = meta
                .modified()
                .map(|t| {
                    t.duration_since(std::time::UNIX_EPOCH)
                        .unwrap_or_default()
                        .as_secs()
                })
                .unwrap_or(0);
            Ok(ContentSignature {
                method: "timestamp".into(),
                value: modified.to_string(),
            })
        }
    }
}

/// Resolve which methods to compute for a given method string list.
/// Defaults to BLAKE3 hash if no methods specified.
pub fn resolve_methods(methods: &[String]) -> Result<Vec<FreshnessMethod>, StampError> {
    if methods.is_empty() {
        // Default to blake3 hash via parse_method which respects feature flags
        return Ok(vec![hash::parse_method("hash")?]);
    }
    methods
        .iter()
        .map(|m| hash::parse_method(m).map_err(StampError::from))
        .collect()
}

/// Record signatures for files into the store.
pub fn record(
    store: &ContentStore,
    files: &[&Path],
    methods: &[FreshnessMethod],
) -> Result<Vec<(String, Vec<ContentSignature>)>, StampError> {
    let mut results = Vec::new();
    for &file in files {
        let mut sigs = Vec::new();
        for &method in methods {
            let sig = compute_signature(file, method)?;
            store.record(file, &sig)?;
            sigs.push(sig);
        }
        results.push((file.display().to_string(), sigs));
    }
    Ok(results)
}

/// Query stored signatures for files.
pub fn query(
    store: &ContentStore,
    files: &[&Path],
) -> Result<Vec<(String, Vec<ContentSignature>)>, StampError> {
    let mut results = Vec::new();
    for &file in files {
        let sigs = store.query(file)?.unwrap_or_default();
        results.push((file.display().to_string(), sigs));
    }
    Ok(results)
}

/// Diff current file contents against stored signatures.
/// Returns (filename, method, changed: bool) tuples.
pub fn diff(
    store: &ContentStore,
    files: &[&Path],
    methods: &[FreshnessMethod],
) -> Result<Vec<(String, String, bool)>, StampError> {
    let mut results = Vec::new();
    for &file in files {
        for &method in methods {
            let current = compute_signature(file, method)?;
            let changed = store.differs(file, &current)?;
            results.push((file.display().to_string(), current.method, changed));
        }
    }
    Ok(results)
}

/// Write signature results to a FormatWriter.
pub fn write_signatures<W: io::Write>(
    writer: &mut FormatWriter<W>,
    results: &[(String, Vec<ContentSignature>)],
) -> Result<(), StampError> {
    for (file, sigs) in results {
        for sig in sigs {
            let rec = Record::new()
                .field("file", file.as_str())
                .field("method", &sig.method)
                .field("value", &sig.value);
            writer.write_record(&rec)?;
        }
    }
    Ok(())
}

/// Write diff results to a FormatWriter.
pub fn write_diffs<W: io::Write>(
    writer: &mut FormatWriter<W>,
    results: &[(String, String, bool)],
) -> Result<(), StampError> {
    for (file, method, changed) in results {
        let rec = Record::new()
            .field("file", file.as_str())
            .field("method", method.as_str())
            .field("changed", if *changed { "true" } else { "false" });
        writer.write_record(&rec)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use lu_common::hash::{ChecksumAlgorithm, HashAlgorithm};
    use std::fs;

    #[test]
    fn test_compute_signature_blake3() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("test.txt");
        fs::write(&file, "hello world").unwrap();

        let sig = compute_signature(&file, FreshnessMethod::Hash(HashAlgorithm::Blake3)).unwrap();
        assert_eq!(sig.method, "blake3");
        assert!(!sig.value.is_empty());
    }

    #[test]
    fn test_compute_signature_crc32() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("test.txt");
        fs::write(&file, "hello world").unwrap();

        let sig =
            compute_signature(&file, FreshnessMethod::Checksum(ChecksumAlgorithm::Crc32)).unwrap();
        assert_eq!(sig.method, "crc32");
    }

    #[test]
    fn test_compute_signature_size() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("test.txt");
        fs::write(&file, "hello world").unwrap();

        let sig = compute_signature(&file, FreshnessMethod::Size).unwrap();
        assert_eq!(sig.method, "size");
        assert_eq!(sig.value, "11");
    }

    #[test]
    fn test_compute_signature_file_not_found() {
        let result = compute_signature(
            Path::new("/nonexistent/file"),
            FreshnessMethod::Hash(HashAlgorithm::Blake3),
        );
        assert!(result.is_err());
    }

    #[test]
    fn test_record_and_query() {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));
        let file = dir.path().join("data.txt");
        fs::write(&file, "content").unwrap();

        let methods = vec![FreshnessMethod::Hash(HashAlgorithm::Blake3)];
        let recorded = record(&store, &[file.as_path()], &methods).unwrap();
        assert_eq!(recorded.len(), 1);
        assert_eq!(recorded[0].1.len(), 1);

        let queried = query(&store, &[file.as_path()]).unwrap();
        assert_eq!(queried[0].1[0].value, recorded[0].1[0].value);
    }

    #[test]
    fn test_diff_unchanged() {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));
        let file = dir.path().join("data.txt");
        fs::write(&file, "content").unwrap();

        let methods = vec![FreshnessMethod::Hash(HashAlgorithm::Blake3)];
        record(&store, &[file.as_path()], &methods).unwrap();

        let diffs = diff(&store, &[file.as_path()], &methods).unwrap();
        assert_eq!(diffs.len(), 1);
        assert!(!diffs[0].2); // not changed
    }

    #[test]
    fn test_diff_changed() {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));
        let file = dir.path().join("data.txt");
        fs::write(&file, "content v1").unwrap();

        let methods = vec![FreshnessMethod::Hash(HashAlgorithm::Blake3)];
        record(&store, &[file.as_path()], &methods).unwrap();

        fs::write(&file, "content v2").unwrap();
        let diffs = diff(&store, &[file.as_path()], &methods).unwrap();
        assert_eq!(diffs.len(), 1);
        assert!(diffs[0].2); // changed
    }

    #[test]
    fn test_multiple_methods() {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));
        let file = dir.path().join("data.txt");
        fs::write(&file, "multi method test").unwrap();

        let methods = vec![
            FreshnessMethod::Hash(HashAlgorithm::Blake3),
            FreshnessMethod::Checksum(ChecksumAlgorithm::Crc32),
            FreshnessMethod::Size,
        ];
        let recorded = record(&store, &[file.as_path()], &methods).unwrap();
        assert_eq!(recorded[0].1.len(), 3);

        let queried = query(&store, &[file.as_path()]).unwrap();
        assert_eq!(queried[0].1.len(), 3);
    }
}
