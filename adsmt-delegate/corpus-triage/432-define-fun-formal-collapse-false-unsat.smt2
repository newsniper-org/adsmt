; The direction the release note does NOT mention.  If every call to a macro
; collapses to the SAME free-parameter body, two calls that should be
; INDEPENDENT become one shared constraint — and two independently-true facts
; become a contradiction.  Both assertions below are true, so the script is
; SAT; corrupted, it is `(= n 5)` and `(not (= n 5))`.
(set-logic QF_LIA)
(define-fun isfive ((k Int)) Bool (= k 5))
(assert (isfive 5))
(assert (not (isfive 6)))
(check-sat)
