; v0.3.2: the non-convex case — no single value entailed (1<=x<=2 with
; f(1)=f(2)=a but neither x=1 nor x=2 alone).
(set-logic QF_UFLIA)
(declare-fun x () Int) (declare-fun a () Int)
(declare-fun f (Int) Int)
(assert (<= 1 x)) (assert (<= x 2))
(assert (= (f 1) a)) (assert (= (f 2) a))
(assert (not (= (f x) a)))
(check-sat)
