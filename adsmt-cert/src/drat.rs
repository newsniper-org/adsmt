//! Minimal DRAT proof checker.
//!
//! DRAT (Delete Reverse Asymmetric Tautology) is the de-facto unsat
//! proof format produced by modern SAT solvers including CaDiCaL.
//! Each line is either an addition (clause) or a deletion (`d`
//! prefix). v0.7 ships a minimal RUP (Reverse Unit Propagation)
//! checker — enough to validate the `RAT` skeleton of typical
//! CaDiCaL proofs.
//!
//! A clause is a `Vec<i32>` (positive = positive literal, negative =
//! negation, terminated implicitly). Variables are dense u32 ids.

#[derive(Clone, Debug)]
pub enum DratStep {
    /// Add a clause that follows from the current formula by RUP.
    Add(Vec<i32>),
    /// Delete a previously-added clause.
    Delete(Vec<i32>),
}

#[derive(Default, Debug, Clone)]
pub struct DratProof {
    pub steps: Vec<DratStep>,
}

impl DratProof {
    pub fn new() -> Self { Self::default() }

    pub fn add(&mut self, clause: Vec<i32>) {
        self.steps.push(DratStep::Add(clause));
    }

    pub fn delete(&mut self, clause: Vec<i32>) {
        self.steps.push(DratStep::Delete(clause));
    }

    /// Verify the proof against `initial_clauses`. Returns `true`
    /// iff every `Add` step is RUP-derivable from the active clause
    /// set, and the final step is the empty clause.
    pub fn verify(&self, initial_clauses: &[Vec<i32>]) -> bool {
        let mut active: Vec<Vec<i32>> = initial_clauses.to_vec();
        for step in &self.steps {
            match step {
                DratStep::Add(c) => {
                    if !rup_derivable(&active, c) {
                        return false;
                    }
                    active.push(c.clone());
                    if c.is_empty() {
                        return true;
                    }
                }
                DratStep::Delete(c) => {
                    active.retain(|x| x != c);
                }
            }
        }
        // Proof terminates without empty clause → not a valid unsat proof.
        false
    }
}

/// Test whether `target` follows from `clauses` by Reverse Unit
/// Propagation: assume `target`'s literals all false, then unit-
/// propagate `clauses`; if a conflict arises, `target` is RUP.
fn rup_derivable(clauses: &[Vec<i32>], target: &[i32]) -> bool {
    use std::collections::HashMap;
    let mut assign: HashMap<u32, bool> = HashMap::new();
    // Assume every literal in target is false.
    for &lit in target {
        let var = lit.unsigned_abs();
        let polarity = lit < 0; // negating: if lit=+x we want x=false, so we record false
        let polarity = !polarity ^ false;
        let value = lit <= 0;
        if let Some(&existing) = assign.get(&var)
            && existing != value {
                return true; // immediate conflict
            }
        assign.insert(var, value);
        let _ = polarity;
    }
    // Unit propagation loop.
    loop {
        let mut progress = false;
        for c in clauses {
            let mut unassigned: Option<i32> = None;
            let mut satisfied = false;
            let mut count_unassigned = 0;
            for &lit in c {
                let var = lit.unsigned_abs();
                let polarity = lit > 0;
                match assign.get(&var) {
                    Some(&v) if v == polarity => { satisfied = true; break; }
                    Some(_) => continue,
                    None => {
                        count_unassigned += 1;
                        unassigned = Some(lit);
                    }
                }
            }
            if satisfied { continue; }
            if count_unassigned == 0 {
                return true; // conflict — RUP derivation succeeds
            }
            if count_unassigned == 1 {
                let lit = unassigned.unwrap();
                let var = lit.unsigned_abs();
                let polarity = lit > 0;
                if let Some(&prev) = assign.get(&var) {
                    if prev != polarity { return true; }
                } else {
                    assign.insert(var, polarity);
                    progress = true;
                }
            }
        }
        if !progress { return false; }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_clause_is_unsat_trivially() {
        let initial: Vec<Vec<i32>> = vec![vec![]];
        let mut proof = DratProof::new();
        proof.add(vec![]); // assert empty clause directly
        assert!(proof.verify(&initial));
    }

    #[test]
    fn polarity_contradiction_rup_unsat() {
        // (p) ∧ (¬p) — adding empty clause is RUP-derivable.
        let initial = vec![vec![1], vec![-1]];
        let mut proof = DratProof::new();
        proof.add(vec![]); // empty clause
        assert!(proof.verify(&initial));
    }

    #[test]
    fn missing_empty_clause_means_invalid() {
        let initial = vec![vec![1], vec![-1]];
        let proof = DratProof::new();
        // No steps — verify returns false (proof never asserts empty).
        assert!(!proof.verify(&initial));
    }

    #[test]
    fn invalid_rup_addition_is_rejected() {
        // (p ∨ q) alone — adding ¬p as RUP fails (no contradiction).
        let initial = vec![vec![1, 2]];
        let mut proof = DratProof::new();
        proof.add(vec![-1]); // try to add ¬p as RUP — should fail
        assert!(!proof.verify(&initial));
    }
}
