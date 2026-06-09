(set-logic ALL)
(declare-const x Int)
(assert (and (> x 0) (< x 0)))
(check-sat)
; native lu-smt rc.32.1: sat   (correct: unsat)
; want: unknown / (:reason-unknown "(incomplete ..."))  -> delegate -> unsat
