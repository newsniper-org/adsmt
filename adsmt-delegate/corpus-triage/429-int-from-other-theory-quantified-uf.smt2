(set-logic AUFLIA)
(declare-fun f (Int) Int)
(assert (forall ((i Int)) (and (> (f i) 0) (< (f i) 1))))
(check-sat)
