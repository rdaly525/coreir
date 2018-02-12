;; smt-lib for very simple circuit
;;
;; a -->
;;       And --> Reg -->
;; b -->


(declare-fun and.a () (_BitVec 1))
(declare-fun and.b () (_ BitVec 1))
(declare-fun and.o () (_ BitVec 1))
(declare-fun and.a_N () (_ BitVec 1))
(declare-fun and.b_N () (_ BitVec 1))
(declare-fun and.o_N () (_ BitVec 1))

(declare-fun reg.clk () (_ BitVec 1))
(declare-fun reg.clk_N () (_ BitVec 1))
(declare-fun reg.in () (_ BitVec 1))
(declare-fun reg.in_N () (_ BitVec 1))
(declare-fun reg.out () (_ BitVec 1))
(declare-fun reg.out_N () (_ BitVec 1))

(assert (= (bvand and.a and.b) and.o))
(assert (= (bvand and.a_N and.b_N) and.o_N))

(assert (= and.o reg.in))
(assert (= and.o_N reg.in_N))

(assert (=> ((bvand (bvnot reg.clk) reg.clk_N))
	    (= reg.o_N reg.in)
	    ))
