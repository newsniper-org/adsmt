; #434 minimal — arith and EUF each satisfied, the COMBINATION is not.
;
; `x1` and the literal `3` get the same arithmetic value in the accepted model
; (x0 = 4 forces x1 = 3), but nothing ever tells EUF they are equal, so
; `(f0 x1)` and `(f0 3)` are free to take different values. The reported model
; is therefore not a FUNCTION:  (f0 3) = 0 while (f0 x1) = 1 with x1 = 3.
;
; This is the Nelson-Oppen ARRANGEMENT obligation over the shared sort, and
; nothing in this solver discharges it. `model_based_combination` propagates
; only ENTAILED (fixed) values, and here x1's value is model-CHOSEN.
;
; NOT caused by the #433 int case split: `OXIZ_NO_INT_CASE_SPLIT=1` also
; answers `sat`. The split's randomized z3 differential merely surfaced it.
;
;   ours: sat        z3, cvc5: unsat
(set-logic QF_UFLIA)
(declare-fun x0 () Int) (declare-fun x1 () Int)
(declare-fun a () Int) (declare-fun b () Int)
(declare-fun f0 (Int) Int)
(assert (<= 3 x0)) (assert (<= x0 4))
(assert (= x0 (+ x1 1)))
(assert (= (f0 2) a)) (assert (= (f0 3) a))
(assert (= (f0 x1) b))
(assert (not (= a b)))
(check-sat)
