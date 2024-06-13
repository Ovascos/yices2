(set-info :smt-lib-version 2.6)
(set-logic QF_FFA)
(define-sort FF0 () (_ FiniteField 13))
(define-sort FF1 () (_ FiniteField 3))
(declare-fun x0 () FF0)
(declare-fun x1 () FF0)
(declare-fun x2 () FF0)
(declare-fun x3 () FF0)
(declare-fun x4 () FF0)
(declare-fun x5 () FF0)
(declare-fun x6 () FF0)
(declare-fun x7 () FF0)
(declare-fun y0 () FF1)
(declare-fun y1 () FF1)
(assert
  (let ((let0 (ff.mul (as ff6 FF0) x3 x4 x4)))
  (let ((let1 (ff.mul (as ff4 FF0) x0 x3 x5)))
  (let ((let2 (ff.mul (as ff7 FF0) x1 x5 x5)))
  (let ((let3 (ff.mul (as ff2 FF0) x4 x7)))
  (let ((let4 (ff.mul (as ff11 FF0) x4)))
  (let ((let5 (ff.add let0 let1 let2 let3 let4)))
  (let ((let6 (= let5 (as ff0 FF0))))
  (let ((let7 (ff.mul (as ff6 FF0) x1 x1 x2)))
  (let ((let8 (ff.mul (as ff7 FF0) x4 x4 x7)))
  (let ((let9 (ff.mul (as ff6 FF0) x0 x6 x7)))
  (let ((let10 (ff.mul (as ff9 FF0) x4 x6)))
  (let ((let11 (ff.mul (as ff11 FF0) x5 x6)))
  (let ((let12 (ff.add let7 let8 let9 let10 let11)))
  (let ((let13 (= let12 (as ff0 FF0))))
  (let ((let14 (ff.mul (as ff9 FF0) x1 x1 x2)))
  (let ((let15 (ff.mul x3 x3 x4)))
  (let ((let16 (ff.mul (as ff11 FF0) x0 x2 x5)))
  (let ((let17 (ff.mul (as ff10 FF0) x0 x0 x6)))
  (let ((let18 (ff.mul (as ff4 FF0) x1 x3 x7)))
  (let ((let19 (as ff9 FF0)))
  (let ((let20 (ff.add let14 let15 let16 let17 let18 let19)))
  (let ((let21 (= let20 (as ff0 FF0))))
  (let ((let22 (ff.mul (as ff5 FF0) x1 x2 x4)))
  (let ((let23 (ff.mul (as ff5 FF0) x1 x4 x6)))
  (let ((let24 (ff.mul x2 x4 x6)))
  (let ((let25 (ff.mul (as ff5 FF0) x4 x6 x6)))
  (let ((let26 (ff.mul (as ff6 FF0) x2 x4)))
  (let ((let27 (ff.add let22 let23 let24 let25 let26)))
  (let ((let28 (= let27 (as ff0 FF0))))
  (let ((let29 (and let6 let13 let21 let28)))
  let29
))))))))))))))))))))))))))))))
)
(assert
 (= y0 (ff.add y1 (as ff1 FF1)))
)
(check-sat)
