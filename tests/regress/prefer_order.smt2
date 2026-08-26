; The preference list is scanned in input order: the first unassigned
; literal wins. a and b are mutually exclusive, and both are preferred.
; a comes first, so a is decided true and b is propagated to false.
; Without the preferences -- or if the list order were not honoured --
; the default heuristic picks the negative phase for a instead, giving
; (a false) (b true).
(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (or a b))
(assert (or (not a) (not b)))
(assert (or a b c))
(prefer a)
(prefer b)
(check-sat)
(get-value (a b c))
(exit)
