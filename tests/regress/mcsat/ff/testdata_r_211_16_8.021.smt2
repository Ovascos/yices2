
(set-info :smt-lib-version 2.6)
(set-logic QF_FFA)
(define-sort FF0 () (_ FiniteField 211))
(declare-fun x0 () FF0)
(declare-fun x1 () FF0)
(declare-fun x2 () FF0)
(declare-fun x3 () FF0)
(declare-fun x4 () FF0)
(declare-fun x5 () FF0)
(declare-fun x6 () FF0)
(declare-fun x7 () FF0)
(declare-fun x8 () FF0)
(declare-fun x9 () FF0)
(declare-fun x10 () FF0)
(declare-fun x11 () FF0)
(declare-fun x12 () FF0)
(declare-fun x13 () FF0)
(declare-fun x14 () FF0)
(declare-fun x15 () FF0)
(assert
  (let ((let0 (ff.mul x8 x8 x13)))
  (let ((let1 (ff.mul (as ff93 FF0) x8 x8)))
  (let ((let2 (ff.mul (as ff173 FF0) x8 x13)))
  (let ((let3 (ff.mul (as ff53 FF0) x8)))
  (let ((let4 (ff.mul (as ff36 FF0) x13)))
  (let ((let5 (as ff183 FF0)))
  (let ((let6 (ff.add let0 let1 let2 let3 let4 let5)))
  (let ((let7 (= let6 (as ff0 FF0))))
  (let ((let8 (ff.mul x8 x8 x10)))
  (let ((let9 (ff.mul (as ff52 FF0) x8 x8)))
  (let ((let10 (ff.mul (as ff141 FF0) x8 x10)))
  (let ((let11 (ff.mul (as ff158 FF0) x8)))
  (let ((let12 (ff.mul (as ff164 FF0) x10)))
  (let ((let13 (as ff88 FF0)))
  (let ((let14 (ff.add let8 let9 let10 let11 let12 let13)))
  (let ((let15 (= let14 (as ff0 FF0))))
  (let ((let16 (ff.mul x3 x14 x14 x14)))
  (let ((let17 (ff.mul (as ff125 FF0) x3 x14 x14)))
  (let ((let18 (ff.mul (as ff203 FF0) x14 x14 x14)))
  (let ((let19 (ff.mul (as ff32 FF0) x3 x14)))
  (let ((let20 (ff.mul (as ff55 FF0) x14 x14)))
  (let ((let21 (ff.mul (as ff207 FF0) x3)))
  (let ((let22 (ff.mul (as ff166 FF0) x14)))
  (let ((let23 (as ff32 FF0)))
  (let ((let24 (ff.add let16 let17 let18 let19 let20 let21 let22 let23)))
  (let ((let25 (= let24 (as ff0 FF0))))
  (let ((let26 (ff.mul x3 x3)))
  (let ((let27 (ff.mul (as ff88 FF0) x3)))
  (let ((let28 (as ff201 FF0)))
  (let ((let29 (ff.add let26 let27 let28)))
  (let ((let30 (= let29 (as ff0 FF0))))
  (let ((let31 (ff.mul x10 x14 x14 x14)))
  (let ((let32 (ff.mul (as ff107 FF0) x10 x14 x14)))
  (let ((let33 (ff.mul (as ff172 FF0) x14 x14 x14)))
  (let ((let34 (ff.mul (as ff146 FF0) x10 x14)))
  (let ((let35 (ff.mul (as ff47 FF0) x14 x14)))
  (let ((let36 (ff.mul (as ff128 FF0) x10)))
  (let ((let37 (ff.mul (as ff3 FF0) x14)))
  (let ((let38 (as ff72 FF0)))
  (let ((let39 (ff.add let31 let32 let33 let34 let35 let36 let37 let38)))
  (let ((let40 (= let39 (as ff0 FF0))))
  (let ((let41 (ff.mul x0 x0 x0 x6 x6 x9 x9)))
  (let ((let42 (ff.mul (as ff154 FF0) x0 x0 x0 x6 x6 x9)))
  (let ((let43 (ff.mul (as ff96 FF0) x0 x0 x0 x6 x9 x9)))
  (let ((let44 (ff.mul (as ff16 FF0) x0 x0 x6 x6 x9 x9)))
  (let ((let45 (ff.mul (as ff133 FF0) x0 x0 x0 x6 x6)))
  (let ((let46 (ff.mul (as ff14 FF0) x0 x0 x0 x6 x9)))
  (let ((let47 (ff.mul (as ff143 FF0) x0 x0 x6 x6 x9)))
  (let ((let48 (ff.mul (as ff23 FF0) x0 x0 x0 x9 x9)))
  (let ((let49 (ff.mul (as ff59 FF0) x0 x0 x6 x9 x9)))
  (let ((let50 (ff.mul (as ff21 FF0) x0 x6 x6 x9 x9)))
  (let ((let51 (ff.mul (as ff108 FF0) x0 x0 x0 x6)))
  (let ((let52 (ff.mul (as ff18 FF0) x0 x0 x6 x6)))
  (let ((let53 (ff.mul (as ff166 FF0) x0 x0 x0 x9)))
  (let ((let54 (ff.mul (as ff13 FF0) x0 x0 x6 x9)))
  (let ((let55 (ff.mul (as ff69 FF0) x0 x6 x6 x9)))
  (let ((let56 (ff.mul (as ff157 FF0) x0 x0 x9 x9)))
  (let ((let57 (ff.mul (as ff117 FF0) x0 x6 x9 x9)))
  (let ((let58 (ff.mul (as ff180 FF0) x6 x6 x9 x9)))
  (let ((let59 (ff.mul (as ff105 FF0) x0 x0 x0)))
  (let ((let60 (ff.mul (as ff40 FF0) x0 x0 x6)))
  (let ((let61 (ff.mul (as ff50 FF0) x0 x6 x6)))
  (let ((let62 (ff.mul (as ff124 FF0) x0 x0 x9)))
  (let ((let63 (ff.mul (as ff83 FF0) x0 x6 x9)))
  (let ((let64 (ff.mul (as ff79 FF0) x6 x6 x9)))
  (let ((let65 (ff.mul (as ff61 FF0) x0 x9 x9)))
  (let ((let66 (ff.mul (as ff189 FF0) x6 x9 x9)))
  (let ((let67 (ff.mul (as ff203 FF0) x0 x0)))
  (let ((let68 (ff.mul (as ff158 FF0) x0 x6)))
  (let ((let69 (ff.mul (as ff97 FF0) x6 x6)))
  (let ((let70 (ff.mul (as ff110 FF0) x0 x9)))
  (let ((let71 (ff.mul (as ff199 FF0) x6 x9)))
  (let ((let72 (ff.mul (as ff131 FF0) x9 x9)))
  (let ((let73 (ff.mul (as ff95 FF0) x0)))
  (let ((let74 (ff.mul (as ff28 FF0) x6)))
  (let ((let75 (ff.mul (as ff129 FF0) x9)))
  (let ((let76 (as ff121 FF0)))
  (let ((let77 (ff.add let41 let42 let43 let44 let45 let46 let47 let48 let49 let50 let51 let52 let53 let54 let55 let56 let57 let58 let59 let60 let61 let62 let63 let64 let65 let66 let67 let68 let69 let70 let71 let72 let73 let74 let75 let76)))
  (let ((let78 (= let77 (as ff0 FF0))))
  (let ((let79 (ff.mul x7 x7 x7)))
  (let ((let80 (ff.mul (as ff98 FF0) x7 x7)))
  (let ((let81 (ff.mul (as ff72 FF0) x7)))
  (let ((let82 (as ff44 FF0)))
  (let ((let83 (ff.add let79 let80 let81 let82)))
  (let ((let84 (= let83 (as ff0 FF0))))
  (let ((let85 (ff.mul x9 x9 x9)))
  (let ((let86 (ff.mul (as ff69 FF0) x9 x9)))
  (let ((let87 (ff.mul (as ff180 FF0) x9)))
  (let ((let88 (as ff65 FF0)))
  (let ((let89 (ff.add let85 let86 let87 let88)))
  (let ((let90 (= let89 (as ff0 FF0))))
  (let ((let91 (and let7 let15 let25 let30 let40 let78 let84 let90)))
  let91
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)
(check-sat)
