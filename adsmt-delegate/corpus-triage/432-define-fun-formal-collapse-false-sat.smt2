; v0.3.2: expanding a define-fun call re-derived each formal from its bare name
; with a Bool fallback, so a non-Bool parameter substituted nothing and stayed
; free in the "expanded" body.
(set-logic QF_LIA)
(define-fun double ((n Int)) Int (+ n n))
(declare-fun z () Int)
(assert (= z 5))
(assert (not (= (double z) 10)))
(check-sat)
