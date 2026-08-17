; #431 MINIMAL — EUF false-SAT, ours=sat / upstream+z3+cvc5=unsat.
; NOT incremental: no push/pop, single check-sat, level 0 only.
;   a = b, so g(b,a) and g(a,a) are congruent, so g(a,a) = g(b,a) != g(a,a).
; Root cause: EufSolver::propagate BATCHES signature updates to the end of the
; use-list scan (oxiz-theories/src/euf/solver.rs:764,875-894), so two parents
; that acquire the SAME new signature within one merge event never see each
; other in sig_table and no congruence merge is enqueued.
; Trigger predicate: one application holds arguments from BOTH merging classes,
; putting both congruent parents in the LOSING class's use-list.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun g (U U) U)
(assert (not (= (g b a) (g a a))))
(assert (= a b))
(check-sat)
(exit)
