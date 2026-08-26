; 'prefer' is a Yices command name. Check that it still works as an
; ordinary symbol everywhere else: as a sort constructor, as a sort
; parameter, as a function name, as a bound variable, and as an
; attribute value.
(set-logic QF_AUFLIA)
(set-info :notes prefer)
(set-info :extra (prefer 1))
(define-sort prefer (X) (Array Int X))
(declare-fun m () (prefer Int))
(declare-fun prefer (Int) Bool)
(declare-fun other () Bool)
(define-fun f ((prefer Int)) Int (+ prefer 1))
(assert (or (prefer 0) other))
(assert (= (select m 0) (f 1)))
(assert (let ((prefer (select m 0))) (> prefer 0)))
(prefer (prefer 0))
(check-sat)
(get-value (other (prefer 0)))
(exit)
