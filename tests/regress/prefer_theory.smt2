; A preference on an arithmetic atom must survive the branching
; heuristic. QF_LRA defaults to BRANCHING_THEORY, so without the
; bypass in special_search the simplex solver would re-pick the sign
; and the preference would be lost.
;   x is preferred low, y is left to the default heuristic.
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (or (<= x (- 5)) (>= x 5)))
(assert (or (<= y (- 5)) (>= y 5)))
(prefer (<= x (- 5)))
(check-sat)
(get-value (x y))
(exit)
