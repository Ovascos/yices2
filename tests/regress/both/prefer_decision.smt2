; (prefer ...) must steer the decision heuristic in both engines.
; The two default heuristics disagree -- DPLL(T) tries the negative
; phase first, MC-SAT the positive one -- so this file states one
; preference of each polarity. Without them, DPLL(T) reports
; (a false) and MC-SAT reports (e true); with them both engines
; agree on the preferred assignment below.
(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun e () Bool)
(declare-fun f () Bool)
(assert (or a b))
(assert (or e f))
(prefer a)
(prefer (not e))
(check-sat)
(get-value (a e))
(exit)
