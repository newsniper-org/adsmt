; #431b, smallest form: no theory at all.  p AND NOT p, then a bare push/pop.
; ours = sat, upstream v0.3.2 = unknown, z3 + cvc5 = unsat.
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(assert (not p))
(push 1)
(pop 1)
(check-sat)
(exit)
