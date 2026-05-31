use lu_common::hash::FreshnessMethod;
use lu_common::store::ContentStore;
use stamp::StampError;
use std::fs;
use std::path::Path;

/// How to combine multiple freshness methods.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CombineMode {
    /// Stale if ANY method says stale (default, conservative)
    Any,
    /// Stale only if ALL methods agree it's stale
    All,
}

/// Check if a target is fresh relative to its dependencies.
///
/// Returns `true` if the target is fresh (up to date), `false` if stale.
///
/// For timestamp method: target is fresh if it exists and is newer than all deps.
/// For hash/checksum/size methods: target is fresh if its stored signature matches current.
/// For always method: always returns false (stale).
pub fn is_fresh(
    store: &ContentStore,
    target: &Path,
    deps: &[&Path],
    methods: &[FreshnessMethod],
    combine: CombineMode,
) -> Result<bool, StampError> {
    if methods.is_empty() {
        return Ok(false);
    }

    // If target doesn't exist, always stale
    if !target.exists() {
        return Ok(false);
    }

    let mut method_results = Vec::new();

    for &method in methods {
        let fresh = match method {
            FreshnessMethod::Always => false,
            FreshnessMethod::Timestamp => is_fresh_by_timestamp(target, deps)?,
            _ => is_fresh_by_content(store, target, deps, method)?,
        };
        method_results.push(fresh);
    }

    let result = match combine {
        CombineMode::Any => method_results.iter().all(|&f| f), // fresh only if ALL methods say fresh
        CombineMode::All => method_results.iter().any(|&f| f), // fresh if ANY method says fresh
    };

    Ok(result)
}

/// Timestamp-based freshness: target is fresh if newer than all deps.
fn is_fresh_by_timestamp(target: &Path, deps: &[&Path]) -> Result<bool, StampError> {
    let target_mtime = fs::metadata(target)
        .and_then(|m| m.modified())
        .map_err(|_| StampError::FileNotFound(target.display().to_string()))?;

    for &dep in deps {
        let dep_mtime = fs::metadata(dep)
            .and_then(|m| m.modified())
            .map_err(|_| StampError::FileNotFound(dep.display().to_string()))?;

        if dep_mtime >= target_mtime {
            return Ok(false); // dep is newer or same age -> stale
        }
    }
    Ok(true)
}

/// Content-based freshness: target is fresh if its stored signature matches current,
/// AND all deps' stored signatures match current (nothing has changed).
fn is_fresh_by_content(
    store: &ContentStore,
    target: &Path,
    deps: &[&Path],
    method: FreshnessMethod,
) -> Result<bool, StampError> {
    // Check target
    let target_sig = stamp::compute_signature(target, method)?;
    if store.differs(target, &target_sig)? {
        return Ok(false);
    }

    // Check all deps
    for &dep in deps {
        if !dep.exists() {
            return Ok(false); // missing dep -> stale
        }
        let dep_sig = stamp::compute_signature(dep, method)?;
        if store.differs(dep, &dep_sig)? {
            return Ok(false); // dep changed -> stale
        }
    }

    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use lu_common::hash::HashAlgorithm;
    use std::fs;
    use std::thread;
    use std::time::Duration;

    fn setup() -> (tempfile::TempDir, ContentStore) {
        let dir = tempfile::tempdir().unwrap();
        let store = ContentStore::new(dir.path().join(".lu-store"));
        (dir, store)
    }

    #[test]
    fn test_fresh_target_not_exists() {
        let (_dir, store) = setup();
        let methods = vec![FreshnessMethod::Timestamp];
        let result = is_fresh(
            &store,
            Path::new("/nonexistent"),
            &[],
            &methods,
            CombineMode::Any,
        )
        .unwrap();
        assert!(!result);
    }

    #[test]
    fn test_fresh_always_stale() {
        let (dir, store) = setup();
        let target = dir.path().join("target.o");
        fs::write(&target, "obj").unwrap();
        let methods = vec![FreshnessMethod::Always];
        let result = is_fresh(&store, &target, &[], &methods, CombineMode::Any).unwrap();
        assert!(!result);
    }

    #[test]
    fn test_fresh_by_timestamp_newer_target() {
        let (dir, store) = setup();
        let dep = dir.path().join("source.c");
        fs::write(&dep, "int main() {}").unwrap();
        thread::sleep(Duration::from_millis(50));
        let target = dir.path().join("target.o");
        fs::write(&target, "obj").unwrap();

        let methods = vec![FreshnessMethod::Timestamp];
        let result =
            is_fresh(&store, &target, &[dep.as_path()], &methods, CombineMode::Any).unwrap();
        assert!(result); // target is newer -> fresh
    }

    #[test]
    fn test_fresh_by_timestamp_older_target() {
        let (dir, store) = setup();
        let target = dir.path().join("target.o");
        fs::write(&target, "obj").unwrap();
        thread::sleep(Duration::from_millis(50));
        let dep = dir.path().join("source.c");
        fs::write(&dep, "int main() { return 1; }").unwrap();

        let methods = vec![FreshnessMethod::Timestamp];
        let result =
            is_fresh(&store, &target, &[dep.as_path()], &methods, CombineMode::Any).unwrap();
        assert!(!result); // dep is newer -> stale
    }

    #[test]
    fn test_fresh_by_hash_unchanged() {
        let (dir, store) = setup();
        let dep = dir.path().join("source.c");
        fs::write(&dep, "int main() {}").unwrap();
        let target = dir.path().join("target.o");
        fs::write(&target, "obj").unwrap();

        let methods = vec![FreshnessMethod::Hash(HashAlgorithm::Blake3)];

        // Record signatures
        stamp::record(
            &store,
            &[target.as_path(), dep.as_path()],
            &methods,
        )
        .unwrap();

        // Check freshness - nothing changed
        let result =
            is_fresh(&store, &target, &[dep.as_path()], &methods, CombineMode::Any).unwrap();
        assert!(result);
    }

    #[test]
    fn test_fresh_by_hash_dep_changed() {
        let (dir, store) = setup();
        let dep = dir.path().join("source.c");
        fs::write(&dep, "int main() {}").unwrap();
        let target = dir.path().join("target.o");
        fs::write(&target, "obj").unwrap();

        let methods = vec![FreshnessMethod::Hash(HashAlgorithm::Blake3)];

        // Record
        stamp::record(
            &store,
            &[target.as_path(), dep.as_path()],
            &methods,
        )
        .unwrap();

        // Modify dep
        fs::write(&dep, "int main() { return 1; }").unwrap();

        let result =
            is_fresh(&store, &target, &[dep.as_path()], &methods, CombineMode::Any).unwrap();
        assert!(!result); // dep changed -> stale
    }

    #[test]
    fn test_combine_any() {
        let (dir, store) = setup();
        let dep = dir.path().join("source.c");
        fs::write(&dep, "code").unwrap();
        thread::sleep(Duration::from_millis(50));
        let target = dir.path().join("target.o");
        fs::write(&target, "obj").unwrap();

        // Timestamp says fresh (target newer), Always says stale
        let methods = vec![FreshnessMethod::Timestamp, FreshnessMethod::Always];
        let result =
            is_fresh(&store, &target, &[dep.as_path()], &methods, CombineMode::Any).unwrap();
        // CombineMode::Any = stale if ANY says stale -> stale (Always says stale)
        assert!(!result);
    }

    #[test]
    fn test_combine_all() {
        let (dir, store) = setup();
        let dep = dir.path().join("source.c");
        fs::write(&dep, "code").unwrap();
        thread::sleep(Duration::from_millis(50));
        let target = dir.path().join("target.o");
        fs::write(&target, "obj").unwrap();

        // Timestamp says fresh, Always says stale
        let methods = vec![FreshnessMethod::Timestamp, FreshnessMethod::Always];
        let result =
            is_fresh(&store, &target, &[dep.as_path()], &methods, CombineMode::All).unwrap();
        // CombineMode::All = fresh if ANY method says fresh -> fresh (Timestamp says fresh)
        assert!(result);
    }
}
