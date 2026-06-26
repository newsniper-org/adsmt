; LINT-MATCHLOOP adversarial repro: a SOUND, SAT, terminating program
; whose single quantified axiom satisfies the rule's exact firing predicate
; ("regenerated occurrence on the SAME bound var AND strictly deeper, no fuel guard").
;
; This is the textbook subterm-monotone shape that pervades real datatype/
; height encodings (cf. Verus prelude `prelude_sized_decorate_*`,
; `prelude_check_decrease_*`). The E-graph terminates by congruence dedup:
; once `(p (s x))` is in the e-graph the regenerated trigger `(p (s x))`
; from the instance is already present, so no new ground term is created.
(set-logic UF)
(declare-sort U 0)
(declare-fun s (U) U)          ; a "successor"/constructor on the same sort
(declare-fun p (U) Bool)
(declare-const c U)

; Axiom: p is upward-closed under s.
;   trigger  : (p x)
;   body     : (=> (p x) (p (s x)))
; The body's consequent (p (s x)) is `p` applied to a STRICTLY DEEPER term
; built ONLY from the same bound var x  ->  the rule's firing predicate is
; satisfied exactly (same var, depth(p (s x)) = depth(p x)+1, no fuel_bool).
(assert
 (forall ((x U)) (!
   (=> (p x) (p (s x)))
   :pattern ((p x))
   :qid upward_closed)))

(assert (p c))     ; seed
(check-sat)        ; SAT: M = { p(s^k c)=true for all k, everything else false }
; get-model would show a finite model up to congruence; the axiom does NOT
; force an infinite distinct chain in any *required* model — sat is correct.
