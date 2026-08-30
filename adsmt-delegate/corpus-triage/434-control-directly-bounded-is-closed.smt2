; #434 CONTROL — the same shape with the EUF-shared variable bounded DIRECTLY
; instead of through a cross-link. Answers `unsat` correctly, because #433's
; int case split fires on `x1` itself (its bounds are asserted unit atoms, so
; they reach the `unit_bounds` journal) and the forced value is then entailed.
;
; The contrast with `434-min-arrangement-*.smt2` is the whole diagnosis: the
; solver can reconcile a shared term it can FORCE, and cannot reconcile one it
; merely AGREES with.
;
;   ours: unsat      z3: unsat      (this file must never regress to `sat`)
(set-logic QF_UFLIA)
(declare-fun x1 () Int)
(declare-fun a () Int) (declare-fun b () Int)
(declare-fun f0 (Int) Int)
(assert (<= 2 x1)) (assert (<= x1 3))
(assert (= (f0 2) a)) (assert (= (f0 3) a))
(assert (= (f0 x1) b))
(assert (not (= a b)))
(check-sat)
