
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
  (let ((let0 x10))
  (let ((let1 (as ff200 FF0)))
  (let ((let2 (ff.add let0 let1)))
  (let ((let3 (= let2 (as ff0 FF0))))
  (let ((let4 (ff.mul x5 x5)))
  (let ((let5 (ff.mul (as ff98 FF0) x5)))
  (let ((let6 (as ff14 FF0)))
  (let ((let7 (ff.add let4 let5 let6)))
  (let ((let8 (= let7 (as ff0 FF0))))
  (let ((let9 (ff.mul x5 x6 x6 x6 x15 x15)))
  (let ((let10 (ff.mul (as ff186 FF0) x5 x6 x6 x6 x15)))
  (let ((let11 (ff.mul (as ff176 FF0) x5 x6 x6 x15 x15)))
  (let ((let12 (ff.mul (as ff105 FF0) x6 x6 x6 x15 x15)))
  (let ((let13 (ff.mul (as ff65 FF0) x5 x6 x6 x6)))
  (let ((let14 (ff.mul (as ff31 FF0) x5 x6 x6 x15)))
  (let ((let15 (ff.mul (as ff118 FF0) x6 x6 x6 x15)))
  (let ((let16 (ff.mul (as ff127 FF0) x5 x6 x15 x15)))
  (let ((let17 (ff.mul (as ff123 FF0) x6 x6 x15 x15)))
  (let ((let18 (ff.mul (as ff46 FF0) x5 x6 x6)))
  (let ((let19 (ff.mul (as ff73 FF0) x6 x6 x6)))
  (let ((let20 (ff.mul (as ff201 FF0) x5 x6 x15)))
  (let ((let21 (ff.mul (as ff90 FF0) x6 x6 x15)))
  (let ((let22 (ff.mul (as ff33 FF0) x5 x15 x15)))
  (let ((let23 (ff.mul (as ff42 FF0) x6 x15 x15)))
  (let ((let24 (ff.mul (as ff26 FF0) x5 x6)))
  (let ((let25 (ff.mul (as ff188 FF0) x6 x6)))
  (let ((let26 (ff.mul (as ff19 FF0) x5 x15)))
  (let ((let27 (ff.mul (as ff5 FF0) x6 x15)))
  (let ((let28 (ff.mul (as ff89 FF0) x15 x15)))
  (let ((let29 (ff.mul (as ff35 FF0) x5)))
  (let ((let30 (ff.mul (as ff198 FF0) x6)))
  (let ((let31 (ff.mul (as ff96 FF0) x15)))
  (let ((let32 (as ff88 FF0)))
  (let ((let33 (ff.add let9 let10 let11 let12 let13 let14 let15 let16 let17 let18 let19 let20 let21 let22 let23 let24 let25 let26 let27 let28 let29 let30 let31 let32)))
  (let ((let34 (= let33 (as ff0 FF0))))
  (let ((let35 (ff.mul x1 x1 x1 x14 x14 x14)))
  (let ((let36 (ff.mul (as ff46 FF0) x1 x1 x1 x14 x14)))
  (let ((let37 (ff.mul (as ff54 FF0) x1 x1 x14 x14 x14)))
  (let ((let38 (ff.mul (as ff58 FF0) x1 x1 x1 x14)))
  (let ((let39 (ff.mul (as ff163 FF0) x1 x1 x14 x14)))
  (let ((let40 (ff.mul (as ff63 FF0) x1 x14 x14 x14)))
  (let ((let41 (ff.mul (as ff57 FF0) x1 x1 x1)))
  (let ((let42 (ff.mul (as ff178 FF0) x1 x1 x14)))
  (let ((let43 (ff.mul (as ff155 FF0) x1 x14 x14)))
  (let ((let44 (ff.mul (as ff9 FF0) x14 x14 x14)))
  (let ((let45 (ff.mul (as ff124 FF0) x1 x1)))
  (let ((let46 (ff.mul (as ff67 FF0) x1 x14)))
  (let ((let47 (ff.mul (as ff203 FF0) x14 x14)))
  (let ((let48 (ff.mul (as ff4 FF0) x1)))
  (let ((let49 (ff.mul (as ff100 FF0) x14)))
  (let ((let50 (as ff91 FF0)))
  (let ((let51 (ff.add let35 let36 let37 let38 let39 let40 let41 let42 let43 let44 let45 let46 let47 let48 let49 let50)))
  (let ((let52 (= let51 (as ff0 FF0))))
  (let ((let53 (ff.mul x1 x1 x3 x3 x3 x12 x12 x12)))
  (let ((let54 (ff.mul (as ff107 FF0) x1 x1 x3 x3 x3 x12 x12)))
  (let ((let55 (ff.mul (as ff153 FF0) x1 x1 x3 x3 x12 x12 x12)))
  (let ((let56 (ff.mul (as ff132 FF0) x1 x3 x3 x3 x12 x12 x12)))
  (let ((let57 (ff.mul (as ff199 FF0) x1 x1 x3 x3 x3 x12)))
  (let ((let58 (ff.mul (as ff124 FF0) x1 x1 x3 x3 x12 x12)))
  (let ((let59 (ff.mul (as ff198 FF0) x1 x3 x3 x3 x12 x12)))
  (let ((let60 (ff.mul (as ff139 FF0) x1 x1 x3 x12 x12 x12)))
  (let ((let61 (ff.mul (as ff151 FF0) x1 x3 x3 x12 x12 x12)))
  (let ((let62 (ff.mul (as ff127 FF0) x3 x3 x3 x12 x12 x12)))
  (let ((let63 (ff.mul (as ff13 FF0) x1 x1 x3 x3 x3)))
  (let ((let64 (ff.mul (as ff63 FF0) x1 x1 x3 x3 x12)))
  (let ((let65 (ff.mul (as ff104 FF0) x1 x3 x3 x3 x12)))
  (let ((let66 (ff.mul (as ff103 FF0) x1 x1 x3 x12 x12)))
  (let ((let67 (ff.mul (as ff121 FF0) x1 x3 x3 x12 x12)))
  (let ((let68 (ff.mul (as ff85 FF0) x3 x3 x3 x12 x12)))
  (let ((let69 (ff.mul (as ff134 FF0) x1 x1 x12 x12 x12)))
  (let ((let70 (ff.mul (as ff202 FF0) x1 x3 x12 x12 x12)))
  (let ((let71 (ff.mul (as ff19 FF0) x3 x3 x12 x12 x12)))
  (let ((let72 (ff.mul (as ff90 FF0) x1 x1 x3 x3)))
  (let ((let73 (ff.mul (as ff28 FF0) x1 x3 x3 x3)))
  (let ((let74 (ff.mul (as ff20 FF0) x1 x1 x3 x12)))
  (let ((let75 (ff.mul (as ff87 FF0) x1 x3 x3 x12)))
  (let ((let76 (ff.mul (as ff164 FF0) x3 x3 x3 x12)))
  (let ((let77 (ff.mul (as ff201 FF0) x1 x1 x12 x12)))
  (let ((let78 (ff.mul (as ff92 FF0) x1 x3 x12 x12)))
  (let ((let79 (ff.mul (as ff134 FF0) x3 x3 x12 x12)))
  (let ((let80 (ff.mul (as ff175 FF0) x1 x12 x12 x12)))
  (let ((let81 (ff.mul (as ff140 FF0) x3 x12 x12 x12)))
  (let ((let82 (ff.mul (as ff119 FF0) x1 x1 x3)))
  (let ((let83 (ff.mul (as ff64 FF0) x1 x3 x3)))
  (let ((let84 (ff.mul (as ff174 FF0) x3 x3 x3)))
  (let ((let85 (ff.mul (as ff80 FF0) x1 x1 x12)))
  (let ((let86 (ff.mul (as ff108 FF0) x1 x3 x12)))
  (let ((let87 (ff.mul (as ff194 FF0) x3 x3 x12)))
  (let ((let88 (ff.mul (as ff157 FF0) x1 x12 x12)))
  (let ((let89 (ff.mul (as ff210 FF0) x3 x12 x12)))
  (let ((let90 (ff.mul (as ff138 FF0) x12 x12 x12)))
  (let ((let91 (ff.mul (as ff54 FF0) x1 x1)))
  (let ((let92 (ff.mul (as ff94 FF0) x1 x3)))
  (let ((let93 (ff.mul (as ff36 FF0) x3 x3)))
  (let ((let94 (ff.mul (as ff10 FF0) x1 x12)))
  (let ((let95 (ff.mul (as ff8 FF0) x3 x12)))
  (let ((let96 (ff.mul (as ff207 FF0) x12 x12)))
  (let ((let97 (ff.mul (as ff165 FF0) x1)))
  (let ((let98 (ff.mul (as ff132 FF0) x3)))
  (let ((let99 (ff.mul (as ff32 FF0) x12)))
  (let ((let100 (as ff106 FF0)))
  (let ((let101 (ff.add let53 let54 let55 let56 let57 let58 let59 let60 let61 let62 let63 let64 let65 let66 let67 let68 let69 let70 let71 let72 let73 let74 let75 let76 let77 let78 let79 let80 let81 let82 let83 let84 let85 let86 let87 let88 let89 let90 let91 let92 let93 let94 let95 let96 let97 let98 let99 let100)))
  (let ((let102 (= let101 (as ff0 FF0))))
  (let ((let103 (ff.mul x0 x0 x0)))
  (let ((let104 (ff.mul (as ff19 FF0) x0 x0)))
  (let ((let105 (ff.mul (as ff37 FF0) x0)))
  (let ((let106 (as ff176 FF0)))
  (let ((let107 (ff.add let103 let104 let105 let106)))
  (let ((let108 (= let107 (as ff0 FF0))))
  (let ((let109 (ff.mul x3 x3 x12 x12 x12 x14 x14)))
  (let ((let110 (ff.mul (as ff176 FF0) x3 x3 x12 x12 x12 x14)))
  (let ((let111 (ff.mul (as ff144 FF0) x3 x3 x12 x12 x14 x14)))
  (let ((let112 (ff.mul (as ff186 FF0) x3 x12 x12 x12 x14 x14)))
  (let ((let113 (ff.mul (as ff43 FF0) x3 x3 x12 x12 x12)))
  (let ((let114 (ff.mul (as ff24 FF0) x3 x3 x12 x12 x14)))
  (let ((let115 (ff.mul (as ff31 FF0) x3 x12 x12 x12 x14)))
  (let ((let116 (ff.mul (as ff68 FF0) x3 x3 x12 x14 x14)))
  (let ((let117 (ff.mul (as ff198 FF0) x3 x12 x12 x14 x14)))
  (let ((let118 (ff.mul (as ff55 FF0) x12 x12 x12 x14 x14)))
  (let ((let119 (ff.mul (as ff73 FF0) x3 x3 x12 x12)))
  (let ((let120 (ff.mul (as ff191 FF0) x3 x12 x12 x12)))
  (let ((let121 (ff.mul (as ff152 FF0) x3 x3 x12 x14)))
  (let ((let122 (ff.mul (as ff33 FF0) x3 x12 x12 x14)))
  (let ((let123 (ff.mul (as ff185 FF0) x12 x12 x12 x14)))
  (let ((let124 (ff.mul (as ff204 FF0) x3 x3 x14 x14)))
  (let ((let125 (ff.mul (as ff199 FF0) x3 x12 x14 x14)))
  (let ((let126 (ff.mul (as ff113 FF0) x12 x12 x14 x14)))
  (let ((let127 (ff.mul (as ff181 FF0) x3 x3 x12)))
  (let ((let128 (ff.mul (as ff74 FF0) x3 x12 x12)))
  (let ((let129 (ff.mul (as ff44 FF0) x12 x12 x12)))
  (let ((let130 (ff.mul (as ff34 FF0) x3 x3 x14)))
  (let ((let131 (ff.mul (as ff209 FF0) x3 x12 x14)))
  (let ((let132 (ff.mul (as ff54 FF0) x12 x12 x14)))
  (let ((let133 (ff.mul (as ff175 FF0) x3 x14 x14)))
  (let ((let134 (ff.mul (as ff153 FF0) x12 x14 x14)))
  (let ((let135 (ff.mul (as ff121 FF0) x3 x3)))
  (let ((let136 (ff.mul (as ff117 FF0) x3 x12)))
  (let ((let137 (ff.mul (as ff6 FF0) x12 x12)))
  (let ((let138 (ff.mul (as ff205 FF0) x3 x14)))
  (let ((let139 (ff.mul (as ff131 FF0) x12 x14)))
  (let ((let140 (ff.mul (as ff37 FF0) x14 x14)))
  (let ((let141 (ff.mul (as ff140 FF0) x3)))
  (let ((let142 (ff.mul (as ff38 FF0) x12)))
  (let ((let143 (ff.mul (as ff182 FF0) x14)))
  (let ((let144 (as ff114 FF0)))
  (let ((let145 (ff.add let109 let110 let111 let112 let113 let114 let115 let116 let117 let118 let119 let120 let121 let122 let123 let124 let125 let126 let127 let128 let129 let130 let131 let132 let133 let134 let135 let136 let137 let138 let139 let140 let141 let142 let143 let144)))
  (let ((let146 (= let145 (as ff0 FF0))))
  (let ((let147 (ff.mul x3 x3 x8 x8 x13 x13 x13)))
  (let ((let148 (ff.mul (as ff161 FF0) x3 x3 x8 x8 x13 x13)))
  (let ((let149 (ff.mul (as ff178 FF0) x3 x3 x8 x13 x13 x13)))
  (let ((let150 (ff.mul (as ff4 FF0) x3 x8 x8 x13 x13 x13)))
  (let ((let151 (ff.mul (as ff121 FF0) x3 x3 x8 x8 x13)))
  (let ((let152 (ff.mul (as ff173 FF0) x3 x3 x8 x13 x13)))
  (let ((let153 (ff.mul (as ff11 FF0) x3 x8 x8 x13 x13)))
  (let ((let154 (ff.mul (as ff69 FF0) x3 x3 x13 x13 x13)))
  (let ((let155 (ff.mul (as ff79 FF0) x3 x8 x13 x13 x13)))
  (let ((let156 (ff.mul (as ff151 FF0) x8 x8 x13 x13 x13)))
  (let ((let157 (ff.mul (as ff36 FF0) x3 x3 x8 x8)))
  (let ((let158 (ff.mul (as ff16 FF0) x3 x3 x8 x13)))
  (let ((let159 (ff.mul (as ff62 FF0) x3 x8 x8 x13)))
  (let ((let160 (ff.mul (as ff137 FF0) x3 x3 x13 x13)))
  (let ((let161 (ff.mul (as ff59 FF0) x3 x8 x13 x13)))
  (let ((let162 (ff.mul (as ff46 FF0) x8 x8 x13 x13)))
  (let ((let163 (ff.mul (as ff65 FF0) x3 x13 x13 x13)))
  (let ((let164 (ff.mul (as ff81 FF0) x8 x13 x13 x13)))
  (let ((let165 (ff.mul (as ff78 FF0) x3 x3 x8)))
  (let ((let166 (ff.mul (as ff144 FF0) x3 x8 x8)))
  (let ((let167 (ff.mul (as ff120 FF0) x3 x3 x13)))
  (let ((let168 (ff.mul (as ff64 FF0) x3 x8 x13)))
  (let ((let169 (ff.mul (as ff125 FF0) x8 x8 x13)))
  (let ((let170 (ff.mul (as ff126 FF0) x3 x13 x13)))
  (let ((let171 (ff.mul (as ff170 FF0) x8 x13 x13)))
  (let ((let172 (ff.mul (as ff80 FF0) x13 x13 x13)))
  (let ((let173 (ff.mul (as ff163 FF0) x3 x3)))
  (let ((let174 (ff.mul (as ff101 FF0) x3 x8)))
  (let ((let175 (ff.mul (as ff161 FF0) x8 x8)))
  (let ((let176 (ff.mul (as ff58 FF0) x3 x13)))
  (let ((let177 (ff.mul (as ff95 FF0) x8 x13)))
  (let ((let178 (ff.mul (as ff9 FF0) x13 x13)))
  (let ((let179 (ff.mul (as ff19 FF0) x3)))
  (let ((let180 (ff.mul (as ff173 FF0) x8)))
  (let ((let181 (ff.mul (as ff185 FF0) x13)))
  (let ((let182 (as ff137 FF0)))
  (let ((let183 (ff.add let147 let148 let149 let150 let151 let152 let153 let154 let155 let156 let157 let158 let159 let160 let161 let162 let163 let164 let165 let166 let167 let168 let169 let170 let171 let172 let173 let174 let175 let176 let177 let178 let179 let180 let181 let182)))
  (let ((let184 (= let183 (as ff0 FF0))))
  (let ((let185 (and let3 let8 let34 let52 let102 let108 let146 let184)))
  let185
))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
)
(check-sat)
