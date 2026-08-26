; (prefer ...) drives the decision heuristic: the preferred literal is
; picked first, at the preferred polarity.
;   a/b are preferred, c/d are not, so the c/d pair shows what the
;   default heuristic (negative phase first) does with the same shape.
(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(assert (or a b))
(assert (or c d))
(prefer a)
(check-sat)
(get-value (a b c d))
(exit)
