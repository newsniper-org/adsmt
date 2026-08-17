; #431b MINIMAL — false-SAT present in BOTH our fork AND upstream v0.3.2.
; A bare matched push/pop with NOTHING between it discards a conflict that was
; already established at level 0.  Not EUF: the pure-Boolean version below is
; enough.  Upstream's #431 congruence fix does NOT cover this.
;   ours = sat, upstream = sat (EUF form) / unknown (Bool form), z3+cvc5 = unsat.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(assert (= a (f b)))
(assert (not (= (f b) a)))
(push 1)
(pop 1)
(check-sat)
(exit)
