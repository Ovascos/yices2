; Basic use of the (prefer <term>) extension: preferences on an atom,
; on its negation, and on a compound term. All of them occur in the
; assertions, so all three are accepted.
(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= a (<= x 0)))
(assert (or (not b) (<= y x)))
(assert (! (or a b) :named prefer))
(prefer a)
(prefer (not b))
(prefer (<= x 0))
(check-sat)
(exit)
