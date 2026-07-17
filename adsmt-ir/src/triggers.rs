//! Out-of-band quantifier **trigger** (`:pattern`) metadata.
//!
//! Triggers are MBQI/e-matching *instantiation guidance* — solver-face
//! metadata, never logical content. The kernel `Π` deliberately carries no
//! trigger slot (a trigger cannot change a term's meaning, so it must not
//! participate in conversion/typing); instead a face records each triggered
//! `forall`'s patterns in a side map keyed by the **hash-consed kernel term
//! of the whole quantifier** (the outermost `Π` of its telescope). Because
//! terms are interned, an identical kernel term *is* an identical formula,
//! so a key collision merges as harmless alternative-trigger semantics; the
//! one real ambiguity — the same term read as `∀x,y. P` vs `∀x. ∀y. P` —
//! is kept apart by `arity` (hence the `Vec<QuantTriggers>` per key: the
//! lowering picks the largest arity that peels cleanly).
//!
//! The map is advisory end-to-end: every consumer drops an entry it cannot
//! honor, and never turns one into an error.

use std::collections::HashMap;

use crate::term::Term;

/// The trigger annotation of one quantifier occurrence: the number of
/// telescope binders its patterns are scoped over, plus the trigger groups
/// (`trigger f(x)` → one 1-pattern group; `trigger { p, q }` → one
/// 2-pattern group; a quantifier may carry several groups = alternatives).
/// Pattern terms are ordinary kernel terms over the SAME de Bruijn window
/// as the quantifier body (`Bound(arity-1)` = the first binder).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantTriggers {
    /// How many leading `Π` binders of the keyed term the patterns bind.
    pub arity: usize,
    /// The trigger groups, each a non-empty multi-pattern.
    pub groups: Vec<Vec<Term>>,
}

/// Side map: hash-consed quantifier term → its recorded trigger annotations
/// (one entry per distinct arity; see the module docs).
pub type TriggerMap = HashMap<Term, Vec<QuantTriggers>>;

/// Merge one quantifier's triggers into `map`: same key + same arity unions
/// the groups (alternative triggers; exact-duplicate groups are dropped),
/// a new arity gets its own [`QuantTriggers`] entry.
pub fn record_triggers(map: &mut TriggerMap, key: Term, arity: usize, groups: Vec<Vec<Term>>) {
    let entries = map.entry(key).or_default();
    if let Some(e) = entries.iter_mut().find(|e| e.arity == arity) {
        for g in groups {
            if !e.groups.contains(&g) {
                e.groups.push(g);
            }
        }
    } else {
        entries.push(QuantTriggers { arity, groups });
    }
}
