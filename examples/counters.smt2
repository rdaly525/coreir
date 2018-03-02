(set-logic QF_BV)
;; Init Variable declarations
(declare-fun i00$in0__AT0 () (_ BitVec 16))
(declare-fun i00$in1__AT0 () (_ BitVec 16))
(declare-fun i00$out__AT0 () (_ BitVec 16))
(declare-fun i01$in0__AT0 () (_ BitVec 16))
(declare-fun i01$in1__AT0 () (_ BitVec 16))
(declare-fun i01$out__AT0 () (_ BitVec 16))
(declare-fun i1$in0__AT0 () (_ BitVec 16))
(declare-fun i1$in1__AT0 () (_ BitVec 16))
(declare-fun i1$out__AT0 () (_ BitVec 16))
(declare-fun in_0__AT0 () (_ BitVec 16))
(declare-fun in_1__AT0 () (_ BitVec 16))
(declare-fun in_2__AT0 () (_ BitVec 16))
(declare-fun in_3__AT0 () (_ BitVec 16))
(declare-fun out__AT0 () (_ BitVec 16))

;; Variable declarations
(declare-fun i00$in0__CURR__ () (_ BitVec 16))
(declare-fun i00$in1__CURR__ () (_ BitVec 16))
(declare-fun i00$out__CURR__ () (_ BitVec 16))
(declare-fun i01$in0__CURR__ () (_ BitVec 16))
(declare-fun i01$in1__CURR__ () (_ BitVec 16))
(declare-fun i01$out__CURR__ () (_ BitVec 16))
(declare-fun i1$in0__CURR__ () (_ BitVec 16))
(declare-fun i1$in1__CURR__ () (_ BitVec 16))
(declare-fun i1$out__CURR__ () (_ BitVec 16))
(declare-fun in_0__CURR__ () (_ BitVec 16))
(declare-fun in_1__CURR__ () (_ BitVec 16))
(declare-fun in_2__CURR__ () (_ BitVec 16))
(declare-fun in_3__CURR__ () (_ BitVec 16))
(declare-fun out__CURR__ () (_ BitVec 16))

;; Next Variable declarations
(declare-fun i00$in0__NEXT__ () (_ BitVec 16))
(declare-fun i00$in1__NEXT__ () (_ BitVec 16))
(declare-fun i00$out__NEXT__ () (_ BitVec 16))
(declare-fun i01$in0__NEXT__ () (_ BitVec 16))
(declare-fun i01$in1__NEXT__ () (_ BitVec 16))
(declare-fun i01$out__NEXT__ () (_ BitVec 16))
(declare-fun i1$in0__NEXT__ () (_ BitVec 16))
(declare-fun i1$in1__NEXT__ () (_ BitVec 16))
(declare-fun i1$out__NEXT__ () (_ BitVec 16))
(declare-fun in_0__NEXT__ () (_ BitVec 16))
(declare-fun in_1__NEXT__ () (_ BitVec 16))
(declare-fun in_2__NEXT__ () (_ BitVec 16))
(declare-fun in_3__NEXT__ () (_ BitVec 16))
(declare-fun out__NEXT__ () (_ BitVec 16))

;; Modules definitions
;; START module declaration for instance 'i00' (Module add)
;; SMTAdd (in1, in2, out) = (in0, in1, out)
(assert (= (bvadd i00$in0__CURR__ i00$in1__CURR__) i00$out__CURR__))
(assert (= (bvadd i00$in0__NEXT__ i00$in1__NEXT__) i00$out__NEXT__))

;; END module declaration

;; START module declaration for instance 'i01' (Module add)
;; SMTAdd (in1, in2, out) = (in0, in1, out)
(assert (= (bvadd i01$in0__CURR__ i01$in1__CURR__) i01$out__CURR__))
(assert (= (bvadd i01$in0__NEXT__ i01$in1__NEXT__) i01$out__NEXT__))

;; END module declaration

;; START module declaration for instance 'i1' (Module add)
;; SMTAdd (in1, in2, out) = (in0, in1, out)
(assert (= (bvadd i1$in0__CURR__ i1$in1__CURR__) i1$out__CURR__))
(assert (= (bvadd i1$in0__NEXT__ i1$in1__NEXT__) i1$out__NEXT__))

;; END module declaration

;; START connections definition
(assert (= i00$in0__CURR__ in_0__CURR__))
(assert (= i00$in0__NEXT__ in_0__NEXT__))
(assert (= i00$in1__CURR__ in_1__CURR__))
(assert (= i00$in1__NEXT__ in_1__NEXT__))
(assert (= i1$in0__CURR__ i00$out__CURR__))
(assert (= i1$in0__NEXT__ i00$out__NEXT__))
(assert (= i01$in0__CURR__ in_2__CURR__))
(assert (= i01$in0__NEXT__ in_2__NEXT__))
(assert (= i01$in1__CURR__ in_3__CURR__))
(assert (= i01$in1__NEXT__ in_3__NEXT__))
(assert (= i1$in1__CURR__ i01$out__CURR__))
(assert (= i1$in1__NEXT__ i01$out__NEXT__))
(assert (= out__CURR__ i1$out__CURR__))
(assert (= out__NEXT__ i1$out__NEXT__))
;; END connections definition


