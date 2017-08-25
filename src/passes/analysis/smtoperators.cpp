#include "coreir.h"
#include "coreir-passes/analysis/smtoperators.hpp"
#include <bitset>

using namespace CoreIR;

namespace CoreIR {
  namespace Passes {

    string CURR_PF = "__CURR__";
    string NEXT_PF = "__NEXT__";
    string NL = "\n";
  
    string SMTgetCurr(string var) {return var + CURR_PF; }
    string SMTgetNext(string var) {return var + NEXT_PF; }
    
    SmtBVVar SmtBVVarGetNext(SmtBVVar var) {
      var.setName(SMTgetNext(var.getName()));
      return var;
    }

    SmtBVVar SmtBVVarGetCurr(SmtBVVar var) {
      var.setName(SMTgetCurr(var.getName()));
      return var;
    }

    string SmtBVVarDec(SmtBVVar w) {
      return "(declare-fun " + w.getName() + " () (_ BitVec " + w.dimstr() + "))";
    }
    
    string getSMTbits(unsigned width, int x) {
      bitset<numeric_limits<int>::digits> b(x);
      return "#b" + b.to_string().substr(numeric_limits<int>::digits - width);
    }

    string assert_op(string expr) {
      return "(assert "+ expr + ")";
    }

    string unary_op_eqass(string op, string in, string out) {
      return assert_op("(= (" + op + " " + in + ") " + out + ")");
    }
    
    string binary_op_eqass(string op, string in1, string in2, string out) {
      return assert_op("(= (" + op + " " + in1 + " " + in2 + ") " + out + ")");
    }

    string unary_op(string op, string in) {
      return "(" + op + " " + in + ")";
    }

    string binary_op(string op, string in1, string in2) {
      return "(" + op + " " + in1 + " " + in2 + ")";
    }
    
    string SMTAssign(SmtBVVar vleft, SmtBVVar vright) {
      SmtBVVar vleft_c = SmtBVVarGetCurr(vleft);
      SmtBVVar vright_c = SmtBVVarGetCurr(vright);
      SmtBVVar vleft_n = SmtBVVarGetNext(vleft);
      SmtBVVar vright_n = SmtBVVarGetNext(vright);
      string curr = assert_op(binary_op("=", vleft_c.getExtractName(), vright_c.getExtractName()));
      string next = assert_op(binary_op("=", vleft_n.getExtractName(), vright_n.getExtractName()));
      return curr + NL + next;
    }
    
    string SMTAnd(SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 & in2) = out) & ((in1' & in2') = out')
      string in1 = in1_p.getName();
      string in2 = in2_p.getName();
      string out = out_p.getName();
      string comment = ";; SMTAnd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvand";
      string curr = binary_op_eqass(op, SMTgetCurr(in1), SMTgetCurr(in2), SMTgetCurr(out));
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTOr(SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 | in2) = out) & ((in1' | in2') = out')
      string in1 = in1_p.getName();
      string in2 = in2_p.getName();
      string out = out_p.getName();
      string comment = ";; SMTOr (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvor";
      string curr = binary_op_eqass(op, SMTgetCurr(in1), SMTgetCurr(in2), SMTgetCurr(out));
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTNot(SmtBVVar in_p, SmtBVVar out_p) {
      // INIT: TRUE
      // TRANS: (!in = out) & (!in' = out')
      string in = in_p.getName();
      string out = out_p.getName();
      string comment = ";; SMTNot (in, out) = (" + in + ", " + out + ")";
      string op = "bvnot";
      string curr = unary_op_eqass(op, SMTgetCurr(in), SMTgetCurr(out));
      string next = unary_op_eqass(op, SMTgetNext(in), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTConst(SmtBVVar out_p, string val) {
      string out = out_p.getName();
      string comment = ";; SMTConst (out, val) = (" + out + ", " + val + ")";
      string curr = assert_op("(= " + SMTgetCurr(out) + " " + val + ")");
      string next = assert_op("(= " + SMTgetNext(out) + " " + val + ")");
      return comment + NL + curr + NL + next;
    }

    string SMTAdd(SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 + in2) = out) & ((in1' + in2') = out')
      string in1 = in1_p.getName();
      string in2 = in2_p.getName();
      string out = out_p.getName();
      string comment = ";; SMTAdd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvadd";
      string curr = binary_op_eqass(op, SMTgetCurr(in1), SMTgetCurr(in2), SMTgetCurr(out));
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTConcat(SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 concat in2) = out) & ((in1' concat in2') = out')
      string in1 = in1_p.getName();
      string in2 = in2_p.getName();
      string out = out_p.getName();
      string comment = ";; SMTConcat (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "concat";
      string curr = binary_op_eqass(op, SMTgetCurr(in1), SMTgetCurr(in2), SMTgetCurr(out));
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTReg(SmtBVVar in_p, SmtBVVar clk_p, SmtBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((!clk & clk') -> (out' = in)) & (!(!clk & clk') -> (out' = out))
      string in = in_p.getName();
      string clk = clk_p.getName();
      string out = out_p.getName();      
      string comment = ";; SMTReg (in, clk, out) = (" + in + ", " + clk + ", " + out + ")";
      string trans_1 = "(=> (= (bvand (bvnot " + SMTgetCurr(clk) + ") " + SMTgetNext(clk) + ") #b1) (= " + SMTgetNext(out) + " " + SMTgetCurr(in) + "))";
      string trans_2 = "(=> (not (= (bvand (bvnot " + SMTgetCurr(clk) + ") " + SMTgetNext(clk) + ") #b1)) (= " + SMTgetNext(out) + " " + SMTgetCurr(out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + trans;
    }
    
    string SMTRegPE(SmtBVVar in_p, SmtBVVar clk_p, SmtBVVar out_p, SmtBVVar en_p) {
      // INIT: TRUE
      // TRANS: ((en & !clk & clk') -> (out' = in)) & (!(en & !clk & clk') -> (out' = out))
      string in = in_p.getName();
      string clk = clk_p.getName();
      string out = out_p.getName();      
      string en = en_p.getName();
      string comment = ";; SMTRegPE (in, clk, out, en) = (" + in + ", " + clk + ", " + out + ", " + en + ")";
      string trans_1 = "(=> (= (bvand " + SMTgetCurr(en) + " (bvand (bvnot " + SMTgetCurr(clk) + ") " + SMTgetNext(clk) + ")) #b1) (= " + SMTgetNext(out) + " " + SMTgetCurr(in) + "))";
      string trans_2 = "(=> (not (= (bvand " + SMTgetCurr(en) + " (bvand (bvnot " + SMTgetCurr(clk) + ") " + SMTgetNext(clk) + ")) #b1)) (= " + SMTgetNext(out) + " " + SMTgetCurr(out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + trans;
    }

    string SMTCounter(SmtBVVar clk_p, SmtBVVar en_p, SmtBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((en & !clk & clk') -> (out' = out+1)) & (!(en & !clk & clk') -> (out' = out))
      string clk = clk_p.getName();
      string out = out_p.getName();      
      string en = en_p.getName();
      string one = getSMTbits(stoi(out_p.dimstr()), 1);
      string comment = ";; SMTCounter (clk, en, out) = (" + clk + ", " + en + ", " + out + ")";
      string trans_1 = "(=> (= (bvand " + SMTgetCurr(en) + "(bvand (bvnot " + SMTgetCurr(clk) + ") " + SMTgetNext(clk) + ")) #b1) (= " + SMTgetNext(out) + " (bvadd " + SMTgetCurr(out) + " " + one + ")))";
      string trans_2 = "(=> (not (= (bvand " + SMTgetCurr(en) + "(bvand (bvnot " + SMTgetCurr(clk) + ") " + SMTgetNext(clk) + ")) #b1)) (= " + SMTgetNext(out) + " " + SMTgetCurr(out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + trans;
    }
 
    string SMTSlice(SmtBVVar in_p, SmtBVVar out_p, string low, string high) {
      // INIT: TRUE
      // TRANS: (_ extract high low) in out) & (_ extract high low) in' out')
      string in = in_p.getName();
      string out = out_p.getName();      
      string comment = ";; SMTSlice (in, out, low, high) = (" + in + ", " + out + ", " + low + ", " + high + ")";
      string op = "(_ extract " + high + " " + low + ")";
      string curr = unary_op_eqass(op, SMTgetCurr(in), SMTgetCurr(out));
      string next = unary_op_eqass(op, SMTgetNext(in), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTClock(SmtBVVar clk_p) {
      // INIT: TRUE
      // TRANS: (!clk & clk')
      string clk = clk_p.getName();
      string comment = ";; SMTClock (clk) = (" + clk + ")";
      string trans = "(assert (= " + SMTgetCurr(clk) + " (bvnot " + SMTgetNext(clk) + ")))";
      return comment + NL + trans;
    }
    
  }
}
