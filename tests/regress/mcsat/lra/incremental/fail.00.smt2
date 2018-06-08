(set-logic QF_LRA)
(push 1)
(declare-fun |s0.x| () Real)
(declare-fun |s0.y| () Real)
(declare-fun |s0.n| () Real)
(assert (let ((l0 (= |s0.x| 0))) (let ((l1 (= |s0.y| |s0.n|))) (let ((l2 (> |s0.n| 0))) (let ((l3 (and l0 l1 l2))) l3)))))
(push 1)
(assert (let ((l0 (+ |s0.x| |s0.y|))) (let ((l1 (= l0 |s0.n|))) (let ((l2 (not l1))) l2))))
(check-sat)
(pop 1)
(declare-fun |s1.x| () Real)
(declare-fun |s1.y| () Real)
(declare-fun |s1.n| () Real)
(assert (let ((l0 (= |s0.y| 0))) (let ((l1 (+ |s0.x| 1))) (let ((l2 (ite l0 0 l1))) (let ((l3 (= |s1.x| l2))) (let ((l4 (- |s0.y| 1))) (let ((l5 (ite l0 |s0.x| l4))) (let ((l6 (= |s1.y| l5))) (let ((l7 (= |s1.n| |s0.n|))) (let ((l8 (and l3 l6 l7))) l8))))))))))
(push 1)
(assert (let ((l0 (+ |s1.x| |s1.y|))) (let ((l1 (= l0 |s1.n|))) (let ((l2 (not l1))) l2))))
(check-sat)