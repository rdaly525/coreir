(set-logic QF_BV)
;; Init Variable declarations
(declare-fun c1$out__AT0 () (_ BitVec 16))
(declare-fun a$out__AT0 () (_ BitVec 16))
(declare-fun a$in1__AT0 () (_ BitVec 16))
(declare-fun a$in0__AT0 () (_ BitVec 16))
(declare-fun r$en__AT0 () (_ BitVec 1))
(declare-fun r$out__AT0 () (_ BitVec 16))
(declare-fun r$clk__AT0 () (_ BitVec 1))
(declare-fun r$in__AT0 () (_ BitVec 16))
(declare-fun clk__AT0 () (_ BitVec 1))
(declare-fun en__AT0 () (_ BitVec 1))
(declare-fun out__AT0 () (_ BitVec 16))

(declare-fun count1$c1$out__AT0 () (_ BitVec 16))
(declare-fun slice1$out__AT0 () (_ BitVec 8))
(declare-fun slice1$in__AT0 () (_ BitVec 16))
(declare-fun count0$r$en__AT0 () (_ BitVec 1))
(declare-fun count0$r$out__AT0 () (_ BitVec 16))
(declare-fun count0$r$clk__AT0 () (_ BitVec 1))
(declare-fun count0$r$in__AT0 () (_ BitVec 16))
(declare-fun term$in__AT0 () (_ BitVec 16))
(declare-fun cat$out__AT0 () (_ BitVec 16))
(declare-fun cat$in1__AT0 () (_ BitVec 8))
(declare-fun cat$in0__AT0 () (_ BitVec 8))
(declare-fun count0$c1$out__AT0 () (_ BitVec 16))
(declare-fun neg$out__AT0 () (_ BitVec 16))
(declare-fun neg$in__AT0 () (_ BitVec 16))
(declare-fun count0$a$out__AT0 () (_ BitVec 16))
(declare-fun count0$a$in1__AT0 () (_ BitVec 16))
(declare-fun count0$a$in0__AT0 () (_ BitVec 16))
(declare-fun slice0$out__AT0 () (_ BitVec 8))
(declare-fun slice0$in__AT0 () (_ BitVec 16))
(declare-fun count1$r$en__AT0 () (_ BitVec 1))
(declare-fun count1$r$out__AT0 () (_ BitVec 16))
(declare-fun count1$r$clk__AT0 () (_ BitVec 1))
(declare-fun count1$r$in__AT0 () (_ BitVec 16))
(declare-fun count1$a$out__AT0 () (_ BitVec 16))
(declare-fun count1$a$in1__AT0 () (_ BitVec 16))
(declare-fun count1$a$in0__AT0 () (_ BitVec 16))

;; Variable declarations
(declare-fun c1$out__CURR__ () (_ BitVec 16))
(declare-fun a$out__CURR__ () (_ BitVec 16))
(declare-fun a$in1__CURR__ () (_ BitVec 16))
(declare-fun a$in0__CURR__ () (_ BitVec 16))
(declare-fun r$en__CURR__ () (_ BitVec 1))
(declare-fun r$out__CURR__ () (_ BitVec 16))
(declare-fun r$clk__CURR__ () (_ BitVec 1))
(declare-fun r$in__CURR__ () (_ BitVec 16))
(declare-fun clk__CURR__ () (_ BitVec 1))
(declare-fun en__CURR__ () (_ BitVec 1))
(declare-fun out__CURR__ () (_ BitVec 16))

(declare-fun count1$c1$out__CURR__ () (_ BitVec 16))
(declare-fun slice1$out__CURR__ () (_ BitVec 8))
(declare-fun slice1$in__CURR__ () (_ BitVec 16))
(declare-fun count0$r$en__CURR__ () (_ BitVec 1))
(declare-fun count0$r$out__CURR__ () (_ BitVec 16))
(declare-fun count0$r$clk__CURR__ () (_ BitVec 1))
(declare-fun count0$r$in__CURR__ () (_ BitVec 16))
(declare-fun term$in__CURR__ () (_ BitVec 16))
(declare-fun cat$out__CURR__ () (_ BitVec 16))
(declare-fun cat$in1__CURR__ () (_ BitVec 8))
(declare-fun cat$in0__CURR__ () (_ BitVec 8))
(declare-fun count0$c1$out__CURR__ () (_ BitVec 16))
(declare-fun neg$out__CURR__ () (_ BitVec 16))
(declare-fun neg$in__CURR__ () (_ BitVec 16))
(declare-fun count0$a$out__CURR__ () (_ BitVec 16))
(declare-fun count0$a$in1__CURR__ () (_ BitVec 16))
(declare-fun count0$a$in0__CURR__ () (_ BitVec 16))
(declare-fun slice0$out__CURR__ () (_ BitVec 8))
(declare-fun slice0$in__CURR__ () (_ BitVec 16))
(declare-fun count1$r$en__CURR__ () (_ BitVec 1))
(declare-fun count1$r$out__CURR__ () (_ BitVec 16))
(declare-fun count1$r$clk__CURR__ () (_ BitVec 1))
(declare-fun count1$r$in__CURR__ () (_ BitVec 16))
(declare-fun count1$a$out__CURR__ () (_ BitVec 16))
(declare-fun count1$a$in1__CURR__ () (_ BitVec 16))
(declare-fun count1$a$in0__CURR__ () (_ BitVec 16))

;; Next Variable declarations
(declare-fun c1$out__NEXT__ () (_ BitVec 16))
(declare-fun a$out__NEXT__ () (_ BitVec 16))
(declare-fun a$in1__NEXT__ () (_ BitVec 16))
(declare-fun a$in0__NEXT__ () (_ BitVec 16))
(declare-fun r$en__NEXT__ () (_ BitVec 1))
(declare-fun r$out__NEXT__ () (_ BitVec 16))
(declare-fun r$clk__NEXT__ () (_ BitVec 1))
(declare-fun r$in__NEXT__ () (_ BitVec 16))
(declare-fun clk__NEXT__ () (_ BitVec 1))
(declare-fun en__NEXT__ () (_ BitVec 1))
(declare-fun out__NEXT__ () (_ BitVec 16))

(declare-fun count1$c1$out__NEXT__ () (_ BitVec 16))
(declare-fun slice1$out__NEXT__ () (_ BitVec 8))
(declare-fun slice1$in__NEXT__ () (_ BitVec 16))
(declare-fun count0$r$en__NEXT__ () (_ BitVec 1))
(declare-fun count0$r$out__NEXT__ () (_ BitVec 16))
(declare-fun count0$r$clk__NEXT__ () (_ BitVec 1))
(declare-fun count0$r$in__NEXT__ () (_ BitVec 16))
(declare-fun term$in__NEXT__ () (_ BitVec 16))
(declare-fun cat$out__NEXT__ () (_ BitVec 16))
(declare-fun cat$in1__NEXT__ () (_ BitVec 8))
(declare-fun cat$in0__NEXT__ () (_ BitVec 8))
(declare-fun count0$c1$out__NEXT__ () (_ BitVec 16))
(declare-fun neg$out__NEXT__ () (_ BitVec 16))
(declare-fun neg$in__NEXT__ () (_ BitVec 16))
(declare-fun count0$a$out__NEXT__ () (_ BitVec 16))
(declare-fun count0$a$in1__NEXT__ () (_ BitVec 16))
(declare-fun count0$a$in0__NEXT__ () (_ BitVec 16))
(declare-fun slice0$out__NEXT__ () (_ BitVec 8))
(declare-fun slice0$in__NEXT__ () (_ BitVec 16))
(declare-fun count1$r$en__NEXT__ () (_ BitVec 1))
(declare-fun count1$r$out__NEXT__ () (_ BitVec 16))
(declare-fun count1$r$clk__NEXT__ () (_ BitVec 1))
(declare-fun count1$r$in__NEXT__ () (_ BitVec 16))
(declare-fun count1$a$out__NEXT__ () (_ BitVec 16))
(declare-fun count1$a$in1__NEXT__ () (_ BitVec 16))
(declare-fun count1$a$in0__NEXT__ () (_ BitVec 16))


;; START module declaration for instance 'c1' (Module const)
;; SMTConst (out, val) = (out, #b0000000000000001)
(assert (= c1$out__CURR__ #b0000000000000001))
(assert (= c1$out__NEXT__ #b0000000000000001))
;; END module declaration

;; START module declaration for instance 'a' (Module add)
;; SMTAdd (in1, in2, out) = (in0, in1, out)
(assert (= (bvadd a$in0__CURR__ a$in1__CURR__) a$out__CURR__))
(assert (= (bvadd a$in0__NEXT__ a$in1__NEXT__) a$out__NEXT__))
;; END module declaration

;; START module declaration for instance 'r' (Module reg)
;; SMTRegPE (in, clk, out, en) = (in, clk, out, en)
(assert (= r$out__AT0 #b0000000000000000))
(assert (and (=> (= (bvand r$en__CURR__ (bvand (bvnot r$clk__CURR__) r$clk__NEXT__)) #b1) (= r$out__NEXT__ r$in__CURR__)) (=> (not (= (bvand r$en__CURR__ (bvand (bvnot r$clk__CURR__) r$clk__NEXT__)) #b1)) (= r$out__NEXT__ r$out__CURR__))))
;; END module declaration

;; START connections definition
;; START module declaration for signal 'clk
;; SMTClock (clk) = (clk)
(assert (= #b0 clk__AT0))
(assert (= clk__CURR__ (bvnot clk__NEXT__)))
;; END module declaration

(assert (= r$clk__CURR__ clk__CURR__))
(assert (= r$clk__NEXT__ clk__NEXT__))
(assert (= a$in0__CURR__ c1$out__CURR__))
(assert (= a$in0__NEXT__ c1$out__NEXT__))
(assert (= a$in1__CURR__ r$out__CURR__))
(assert (= a$in1__NEXT__ r$out__NEXT__))
(assert (= r$en__CURR__ en__CURR__))
(assert (= r$en__NEXT__ en__NEXT__))
(assert (= r$in__CURR__ a$out__CURR__))
(assert (= r$in__NEXT__ a$out__NEXT__))
(assert (= out__CURR__ r$out__CURR__))
(assert (= out__NEXT__ r$out__NEXT__))
;; END connections definition



;; START module declaration for instance 'count1$c1' (Module const)
;; SMTConst (out, val) = (out, #b0000000000000001)
(assert (= count1$c1$out__CURR__ #b0000000000000001))
(assert (= count1$c1$out__NEXT__ #b0000000000000001))
;; END module declaration

;; START module declaration for instance 'slice1' (Module slice)
;; SMTSlice (in, out) = (in, out)
(assert (= ((_ extract 15 8) slice1$in__CURR__) slice1$out__CURR__))
(assert (= ((_ extract 15 8) slice1$in__NEXT__) slice1$out__NEXT__))

;; END module declaration

;; START module declaration for instance 'count0$r' (Module reg)
;; SMTRegPE (in, clk, out, en) = (in, clk, out, en)
(assert (= count0$r$out__AT0 #b0000000000000000))
(assert (and (=> (= (bvand count0$r$en__CURR__ (bvand (bvnot count0$r$clk__CURR__) count0$r$clk__NEXT__)) #b1) (= count0$r$out__NEXT__ count0$r$in__CURR__)) (=> (not (= (bvand count0$r$en__CURR__ (bvand (bvnot count0$r$clk__CURR__) count0$r$clk__NEXT__)) #b1)) (= count0$r$out__NEXT__ count0$r$out__CURR__))))
;; END module declaration


;; START module declaration for instance 'cat' (Module concat)
;; SMTConcat (in1, in2, out) = (in0, in1, out)
(assert (= (concat cat$in0__CURR__ cat$in1__CURR__) cat$out__CURR__))
(assert (= (concat cat$in0__NEXT__ cat$in1__NEXT__) cat$out__NEXT__))
;; END module declaration

;; START module declaration for instance 'count0$c1' (Module const)
;; SMTConst (out, val) = (out, #b0000000000000001)
(assert (= count0$c1$out__CURR__ #b0000000000000001))
(assert (= count0$c1$out__NEXT__ #b0000000000000001))
;; END module declaration

;; START module declaration for instance 'neg' (Module neg)
;; SMTNot (in, out) = (in, out)
(assert (= (bvnot neg$in__CURR__) neg$out__CURR__))
(assert (= (bvnot neg$in__NEXT__) neg$out__NEXT__))
;; END module declaration

;; START module declaration for instance 'count0$a' (Module add)
;; SMTAdd (in1, in2, out) = (in0, in1, out)
(assert (= (bvadd count0$a$in0__CURR__ count0$a$in1__CURR__) count0$a$out__CURR__))
(assert (= (bvadd count0$a$in0__NEXT__ count0$a$in1__NEXT__) count0$a$out__NEXT__))
;; END module declaration

;; START module declaration for instance 'slice0' (Module slice)
;; SMTSlice (in, out) = (in, out)
(assert (= ((_ extract 7 0) slice0$in__CURR__) slice0$out__CURR__))
(assert (= ((_ extract 7 0) slice0$in__NEXT__) slice0$out__NEXT__))

;; END module declaration

;; START module declaration for instance 'count1$r' (Module reg)
;; SMTRegPE (in, clk, out, en) = (in, clk, out, en)
(assert (= count1$r$out__AT0 #b0000000000000000))
(assert (and (=> (= (bvand count1$r$en__CURR__ (bvand (bvnot count1$r$clk__CURR__) count1$r$clk__NEXT__)) #b1) (= count1$r$out__NEXT__ count1$r$in__CURR__)) (=> (not (= (bvand count1$r$en__CURR__ (bvand (bvnot count1$r$clk__CURR__) count1$r$clk__NEXT__)) #b1)) (= count1$r$out__NEXT__ count1$r$out__CURR__))))
;; END module declaration

;; START module declaration for instance 'count1$a' (Module add)
;; SMTAdd (in1, in2, out) = (in0, in1, out)
(assert (= (bvadd count1$a$in0__CURR__ count1$a$in1__CURR__) count1$a$out__CURR__))
(assert (= (bvadd count1$a$in0__NEXT__ count1$a$in1__NEXT__) count1$a$out__NEXT__))
;; END module declaration

;; START connections definition
(assert (= slice0$in__CURR__ count0$r$out__CURR__))
(assert (= slice0$in__NEXT__ count0$r$out__NEXT__))
(assert (= count1$r$en__CURR__ ((_ extract 4 4) count0$r$out__CURR__)))
(assert (= count1$r$en__NEXT__ ((_ extract 4 4) count0$r$out__NEXT__)))
(assert (= count0$r$clk__CURR__ clk__CURR__))
(assert (= count0$r$clk__NEXT__ clk__NEXT__))
(assert (= term$in__CURR__ neg$out__CURR__))
(assert (= term$in__NEXT__ neg$out__NEXT__))
(assert (= count0$r$en__CURR__ ((_ extract 8 8) count1$r$out__CURR__)))
(assert (= count0$r$en__NEXT__ ((_ extract 8 8) count1$r$out__NEXT__)))
(assert (= cat$in1__CURR__ slice1$out__CURR__))
(assert (= cat$in1__NEXT__ slice1$out__NEXT__))
(assert (= cat$in0__CURR__ slice0$out__CURR__))
(assert (= cat$in0__NEXT__ slice0$out__NEXT__))
(assert (= count0$a$in0__CURR__ count0$c1$out__CURR__))
(assert (= count0$a$in0__NEXT__ count0$c1$out__NEXT__))
(assert (= slice1$in__CURR__ count1$r$out__CURR__))
(assert (= slice1$in__NEXT__ count1$r$out__NEXT__))
(assert (= count1$a$in1__CURR__ count1$r$out__CURR__))
(assert (= count1$a$in1__NEXT__ count1$r$out__NEXT__))
(assert (= count1$r$in__CURR__ count1$a$out__CURR__))
(assert (= count1$r$in__NEXT__ count1$a$out__NEXT__))
(assert (= neg$in__CURR__ cat$out__CURR__))
(assert (= neg$in__NEXT__ cat$out__NEXT__))
(assert (= count1$a$in0__CURR__ count1$c1$out__CURR__))
(assert (= count1$a$in0__NEXT__ count1$c1$out__NEXT__))
(assert (= count1$r$clk__CURR__ clk__CURR__))
(assert (= count1$r$clk__NEXT__ clk__NEXT__))
(assert (= count0$r$in__CURR__ count0$a$out__CURR__))
(assert (= count0$r$in__NEXT__ count0$a$out__NEXT__))
(assert (= count0$a$in1__CURR__ count0$r$out__CURR__))
(assert (= count0$a$in1__NEXT__ count0$r$out__NEXT__))
;; END connections definition


;; PROPERTIES

;; en & ((!clk & clk') & !(out' = out + 1))
;; (assert (and (= en__CURR__ #b1) (and (= (bvand (bvnot clk__CURR__) clk__NEXT__) #b1) (not (= out__NEXT__ (bvadd out__CURR__ #b0000000000000001))))))


;; en & ((!clk & clk') & (out' = out + 1))
;; (assert (and (= en__CURR__ #b1) (and (= (bvand (bvnot clk__CURR__) clk__NEXT__) #b1) (= out__NEXT__ (bvadd out__CURR__ #b0000000000000001)))))

;; en
;; (assert (= en__CURR__ #b1))



