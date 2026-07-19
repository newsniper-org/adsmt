//! Persistent cross-process memo for [`crate::oxiz`]'s delegation verdicts,
//! rooted at `$ADSMT_DELEGATE_MEMO_DIR` (unset/empty = disabled — the sole
//! switch). Two tiers under `<root>/v0/`:
//!
//! * **Tier-1** — `v0/unsat/<engine-fp>/<script-digest>.json`: "this exact
//!   script was decided `unsat` by this exact engine binary". Keyed by the
//!   K12-256 of the FULL script bytes, namespaced under the K12-256 of the
//!   running binary (`current_exe()` bytes), so an engine change invalidates
//!   every entry by construction: the memo only ever replays a verdict the
//!   very same solver produced — nothing weaker satisfies the unsat-trust
//!   rule ([`crate::oxiz`] module docs).
//! * **Tier-2** — `v0/shape/<decl-digest>`: OUTSIDE the fp namespace.
//!   Sound-by-construction ORDERING guidance ("this obligation family last
//!   proved via the floor shape → try the floor first"), which survives
//!   engine changes because a wrong hint only reorders the two solves, never
//!   decides anything. Keyed by the K12-256 of the FLOOR render's declaration
//!   prefix (everything before the first `(assert `). The floor prefix is
//!   mandatory: the ANNOTATED prefix is pattern-map-dependent (pattern-only
//!   symbols get `declare-fun`s — pinned by
//!   `pattern_only_symbols_are_declared`), so it would split buckets that are
//!   the same obligation family. Content is a single line
//!   `annotated`|`floor`, last-writer-wins.
//!
//! Every operation is infallible-by-swallowing: an unreadable dir, corrupt
//! JSON, a failed write, or an unreadable `current_exe()` degrade to a miss /
//! memo-disabled-for-process — never a panic, and never a verdict this
//! binary did not itself produce.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Which render shape a recorded `unsat` came from / a tier-2 hint suggests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Shape {
    Annotated,
    Floor,
}

impl Shape {
    fn as_str(self) -> &'static str {
        match self {
            Shape::Annotated => "annotated",
            Shape::Floor => "floor",
        }
    }
}

/// Tier-1 entry (serde; NO `deny_unknown_fields` — a future writer may add
/// fields and an old reader must still hit). `instances` is the V1 reserve
/// (recorded instantiations), always `[]` today.
#[derive(serde::Serialize, serde::Deserialize)]
struct Entry {
    v: u32,
    shape: String,
    /// Wall milliseconds of the `run_script` call that produced the verdict.
    guard_ms: u64,
    recorded_unix: u64,
    instances: Vec<serde_json::Value>,
}

/// An enabled memo: the store root + this process's engine fingerprint.
pub(crate) struct Memo {
    root: PathBuf,
    fp_hex: String,
}

impl Memo {
    /// The production constructor: root from `ADSMT_DELEGATE_MEMO_DIR`
    /// (unset/empty = disabled) + the engine-fingerprint gate.
    pub(crate) fn from_env() -> Option<Memo> {
        let root = std::env::var_os("ADSMT_DELEGATE_MEMO_DIR")?;
        if root.is_empty() {
            return None;
        }
        Memo::at(PathBuf::from(root))
    }

    /// Test injection: a memo rooted at `root`. `None` iff the engine
    /// fingerprint is unavailable (memo disabled for the process).
    pub(crate) fn at(root: PathBuf) -> Option<Memo> {
        Some(Memo { root, fp_hex: engine_fingerprint()?.to_owned() })
    }

    /// Tier-1 key: K12-256 hex of the full script bytes.
    pub(crate) fn script_digest(script: &str) -> String {
        lu_common::k12::hex(&lu_common::k12::hash_with_customization(
            script.as_bytes(),
            b"adsmt-delegate-memo-t1-v0",
        ))
    }

    /// Tier-2 key: K12-256 hex of the FLOOR script's declaration prefix (see
    /// the module docs on why the annotated prefix must never be used).
    pub(crate) fn shape_bucket(floor_script: &str) -> String {
        lu_common::k12::hex(&lu_common::k12::hash_with_customization(
            decl_prefix(floor_script).as_bytes(),
            b"adsmt-delegate-memo-shape-v0",
        ))
    }

    /// `true` iff a well-formed `v == 0` entry exists for `digest` under THIS
    /// engine's fingerprint. Unreadable / unparseable / other-version ⇒ miss.
    pub(crate) fn lookup_unsat(&self, digest: &str) -> bool {
        let Ok(bytes) = std::fs::read(self.unsat_path(digest)) else {
            return false;
        };
        matches!(serde_json::from_slice::<Entry>(&bytes), Ok(e) if e.v == 0)
    }

    /// The tier-2 ordering hint for `bucket`, if a clean one exists (trim +
    /// exact match; anything else is no hint).
    pub(crate) fn shape_hint(&self, bucket: &str) -> Option<Shape> {
        let s = std::fs::read_to_string(self.shape_path(bucket)).ok()?;
        match s.trim() {
            "annotated" => Some(Shape::Annotated),
            "floor" => Some(Shape::Floor),
            _ => None,
        }
    }

    /// Record a fresh live `unsat` (never called on a memo hit). `guard_ms`
    /// is the wall time of the recorded `run_script`.
    pub(crate) fn record_unsat(&self, digest: &str, shape: Shape, guard_ms: u64) {
        let entry = Entry {
            v: 0,
            shape: shape.as_str().to_owned(),
            guard_ms,
            recorded_unix: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs())
                .unwrap_or(0),
            instances: Vec::new(),
        };
        let Ok(json) = serde_json::to_vec(&entry) else {
            return;
        };
        write_atomic(&self.unsat_path(digest), digest, &json);
    }

    /// Record which shape proved this bucket (last-writer-wins).
    pub(crate) fn record_shape(&self, bucket: &str, shape: Shape) {
        write_atomic(&self.shape_path(bucket), bucket, shape.as_str().as_bytes());
    }

    fn unsat_path(&self, digest: &str) -> PathBuf {
        self.root.join("v0").join("unsat").join(&self.fp_hex).join(format!("{digest}.json"))
    }

    fn shape_path(&self, bucket: &str) -> PathBuf {
        self.root.join("v0").join("shape").join(bucket)
    }
}

/// The floor script's declaration prefix — everything strictly before the
/// first `(assert ` (the whole script when there is none).
fn decl_prefix(script: &str) -> &str {
    &script[..script.find("(assert ").unwrap_or(script.len())]
}

/// K12-256 hex of the running binary (`current_exe()` bytes) — the tier-1
/// namespace. Same shape as adsmt-cli's `current_binary_sha256`, but K12 +
/// OnceLock-memoized INCLUDING the `None` (unreadable exe ⇒ memo disabled
/// for the process). The whole-binary read costs tens of ms, paid once and
/// only when the memo is enabled.
fn engine_fingerprint() -> Option<&'static str> {
    static FP: OnceLock<Option<String>> = OnceLock::new();
    FP.get_or_init(|| {
        let path = std::env::current_exe().ok()?;
        let bytes = std::fs::read(path).ok()?;
        Some(lu_common::k12::hex(&lu_common::k12::hash_with_customization(
            &bytes,
            b"adsmt-delegate-memo-fp-v0",
        )))
    })
    .as_deref()
}

/// Atomic publish: write `<parent>/.tmp.<pid>.<key[..16]>` then `fs::rename`
/// onto the final path (same-dir tmp ⇒ the rename is atomic on POSIX;
/// rename-over-existing ⇒ last-writer-wins). All errors swallowed — memo
/// writes are best-effort.
fn write_atomic(final_path: &Path, key: &str, bytes: &[u8]) {
    let Some(parent) = final_path.parent() else {
        return;
    };
    if std::fs::create_dir_all(parent).is_err() {
        return;
    }
    let tmp = parent.join(format!(".tmp.{}.{}", std::process::id(), &key[..key.len().min(16)]));
    if std::fs::write(&tmp, bytes).is_err() {
        let _ = std::fs::remove_file(&tmp);
        return;
    }
    if std::fs::rename(&tmp, final_path).is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decl_prefix_stops_at_first_assert() {
        let script = "(set-logic ALL)\n(declare-const x Int)\n(assert (> x 0))\n(assert (not (> x 5)))\n(check-sat)\n";
        assert_eq!(decl_prefix(script), "(set-logic ALL)\n(declare-const x Int)\n");
        // no assert ⇒ the whole script is the prefix.
        assert_eq!(decl_prefix("(set-logic ALL)\n"), "(set-logic ALL)\n");
        // same decl set, different asserts ⇒ same bucket; a different decl
        // set ⇒ a different bucket.
        let same_decls = "(set-logic ALL)\n(declare-const x Int)\n(assert (= x 1))\n(check-sat)\n";
        assert_eq!(Memo::shape_bucket(script), Memo::shape_bucket(same_decls));
        let other_decls = "(set-logic ALL)\n(declare-const y Int)\n(assert (= y 1))\n(check-sat)\n";
        assert_ne!(Memo::shape_bucket(script), Memo::shape_bucket(other_decls));
    }

    #[test]
    fn atomic_write_last_writer_wins() {
        let dir = tempfile::tempdir().expect("tempdir");
        let a = Memo::at(dir.path().to_path_buf()).expect("memo enabled");
        let b = Memo::at(dir.path().to_path_buf()).expect("memo enabled");
        let digest = Memo::script_digest("(check-sat)\n");
        a.record_unsat(&digest, Shape::Annotated, 11);
        b.record_unsat(&digest, Shape::Floor, 22);
        // the final file is the second writer's, and it parses.
        assert!(a.lookup_unsat(&digest));
        let bytes = std::fs::read(a.unsat_path(&digest)).expect("entry file");
        let e: Entry = serde_json::from_slice(&bytes).expect("parseable");
        assert_eq!(e.v, 0);
        assert_eq!(e.shape, "floor");
        assert_eq!(e.guard_ms, 22);
        assert!(e.instances.is_empty());
        // no tmp litter left behind.
        let parent = a.unsat_path(&digest);
        let leftovers = std::fs::read_dir(parent.parent().unwrap())
            .unwrap()
            .filter_map(Result::ok)
            .filter(|d| d.file_name().to_string_lossy().starts_with(".tmp."))
            .count();
        assert_eq!(leftovers, 0, "tmp files must be renamed away");
    }
}
