#include "coreir.h"
#include "coreir-passes/analysis/smvoperators.hpp"
#include <bitset>

using namespace CoreIR;

namespace {
  string INIT_PF = "__AT0";
  string CURR_PF = "__CURR__";
  string NEXT_PF = "__NEXT__";
  string NL = "\n";


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
}

namespace CoreIR {
  namespace Passes {

    string SMVgetInit(string context, string var) {return context + var + INIT_PF; }
    string SMVgetCurr(string context, string var) {return context + var + CURR_PF; }
    string SMVgetNext(string context, string var) {return context + var + NEXT_PF; }

    SmvBVVar SmvBVVarGetInit(SmvBVVar var) {
      var.setName(SMVgetInit("", var.getName()));
      return var;
    }

    SmvBVVar SmvBVVarGetNext(SmvBVVar var) {
      var.setName(SMVgetNext("", var.getName()));
      return var;
    }

    SmvBVVar SmvBVVarGetCurr(SmvBVVar var) {
      var.setName(SMVgetCurr("", var.getName()));
      return var;
    }

    string SmvBVVarDec(SmvBVVar w) {
      return "(declare-fun " + w.getName() + " () (_ BitVec " + w.dimstr() + "))";
    }

    string getSMVbits(unsigned width, int x) {
      bitset<numeric_limits<int>::digits> b(x);
      return "#b" + b.to_string().substr(numeric_limits<int>::digits - width);
    }

    string SMVAssign(SmvBVVar vleft, SmvBVVar vright) {
      SmvBVVar vleft_c = SmvBVVarGetCurr(vleft);
      SmvBVVar vright_c = SmvBVVarGetCurr(vright);
      SmvBVVar vleft_n = SmvBVVarGetNext(vleft);
      SmvBVVar vright_n = SmvBVVarGetNext(vright);
      string curr = assert_op(binary_op("=", vleft_c.getExtractName(), vright_c.getExtractName()));
      string next = assert_op(binary_op("=", vleft_n.getExtractName(), vright_n.getExtractName()));
      return curr + NL + next;
    }

    string SMVAnd(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 & in2) = out) & ((in1' & in2') = out')
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMVAnd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvand";
      string curr = binary_op_eqass(op, SMVgetCurr(context, in1), SMVgetCurr(context, in2), SMVgetCurr(context, out));
      string next = binary_op_eqass(op, SMVgetNext(context, in1), SMVgetNext(context, in2), SMVgetNext(context, out));
      return comment + NL + curr + NL + next;
    }

    string SMVOr(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 | in2) = out) & ((in1' | in2') = out')
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMVOr (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvor";
      string curr = binary_op_eqass(op, SMVgetCurr(context, in1), SMVgetCurr(context, in2), SMVgetCurr(context, out));
      string next = binary_op_eqass(op, SMVgetNext(context, in1), SMVgetNext(context, in2), SMVgetNext(context, out));
      return comment + NL + curr + NL + next;
    }

    string SMVNot(string context, SmvBVVar in_p, SmvBVVar out_p) {
      // INIT: TRUE
      // TRANS: (!in = out) & (!in' = out')
      string in = in_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMVNot (in, out) = (" + in + ", " + out + ")";
      string op = "bvnot";
      string curr = unary_op_eqass(op, SMVgetCurr(context, in), SMVgetCurr(context, out));
      string next = unary_op_eqass(op, SMVgetNext(context, in), SMVgetNext(context, out));
      return comment + NL + curr + NL + next;
    }

    string SMVConst(string context, SmvBVVar out_p, string val) {
      string out = out_p.getPortName();
      string comment = ";; SMVConst (out, val) = (" + out + ", " + val + ")";
      string curr = assert_op("(= " + SMVgetCurr(context, out) + " " + val + ")");
      string next = assert_op("(= " + SMVgetNext(context, out) + " " + val + ")");
      return comment + NL + curr + NL + next;
    }

    string SMVAdd(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 + in2) = out) & ((in1' + in2') = out')
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMVAdd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvadd";
      string curr = binary_op_eqass(op, SMVgetCurr(context, in1), SMVgetCurr(context, in2), SMVgetCurr(context, out));
      string next = binary_op_eqass(op, SMVgetNext(context, in1), SMVgetNext(context, in2), SMVgetNext(context, out));
      return comment + NL + curr + NL + next;
    }

    string SMVConcat(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 concat in2) = out) & ((in1' concat in2') = out')
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMVConcat (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "concat";
      string curr = binary_op_eqass(op, SMVgetCurr(context, in1), SMVgetCurr(context, in2), SMVgetCurr(context, out));
      string next = binary_op_eqass(op, SMVgetNext(context, in1), SMVgetNext(context, in2), SMVgetNext(context, out));
      return comment + NL + curr + NL + next;
    }

    string SMVReg(string context, SmvBVVar in_p, SmvBVVar clk_p, SmvBVVar out_p) {
      // INIT: out = 0
      // TRANS: ((!clk & clk') -> (out' = in)) & (!(!clk & clk') -> (out' = out))
      string in = in_p.getPortName();
      string clk = clk_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMVReg (in, clk, out) = (" + in + ", " + clk + ", " + out + ")";
      string zero = getSMVbits(stoi(out_p.dimstr()), 0);
      string init = assert_op("(= "+SMVgetInit(context, out)+" "+zero+")");
      string trans_1 = "(=> (= (bvand (bvnot " + SMVgetCurr(context, clk) + ") " + SMVgetNext(context, clk) + ") #b1) (= " + SMVgetNext(context, out) + " " + SMVgetCurr(context, in) + "))";
      string trans_2 = "(=> (not (= (bvand (bvnot " + SMVgetCurr(context, clk) + ") " + SMVgetNext(context, clk) + ") #b1)) (= " + SMVgetNext(context, out) + " " + SMVgetCurr(context, out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + init + NL + trans;
    }

    string SMVRegPE(string context, SmvBVVar in_p, SmvBVVar clk_p, SmvBVVar out_p, SmvBVVar en_p) {
      // INIT: out = 0
      // TRANS: ((en & !clk & clk') -> (out' = in)) & (!(en & !clk & clk') -> (out' = out))
      string in = in_p.getPortName();
      string clk = clk_p.getPortName();
      string out = out_p.getPortName();
      string en = en_p.getPortName();
      string comment = ";; SMVRegPE (in, clk, out, en) = (" + in + ", " + clk + ", " + out + ", " + en + ")";
      string zero = getSMVbits(stoi(out_p.dimstr()), 0);
      string init = assert_op("(= "+SMVgetInit(context, out)+" "+zero+")");
      string trans_1 = "(=> (= (bvand " + SMVgetCurr(context, en) + " (bvand (bvnot " + SMVgetCurr(context, clk) + ") " + SMVgetNext(context, clk) + ")) #b1) (= " + SMVgetNext(context, out) + " " + SMVgetCurr(context, in) + "))";
      string trans_2 = "(=> (not (= (bvand " + SMVgetCurr(context, en) + " (bvand (bvnot " + SMVgetCurr(context, clk) + ") " + SMVgetNext(context, clk) + ")) #b1)) (= " + SMVgetNext(context, out) + " " + SMVgetCurr(context, out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + init + NL + trans;
    }

    string SMVCounter(string context, SmvBVVar clk_p, SmvBVVar en_p, SmvBVVar out_p) {
      // INIT: out = 0
      // TRANS: ((en & !clk & clk') -> (out' = out+1)) & (!(en & !clk & clk') -> (out' = out))
      string clk = clk_p.getPortName();
      string out = out_p.getPortName();
      string en = en_p.getPortName();
      string one = getSMVbits(stoi(out_p.dimstr()), 1);
      string comment = ";; SMVCounter (clk, en, out) = (" + clk + ", " + en + ", " + out + ")";
      string zero = getSMVbits(stoi(out_p.dimstr()), 0);
      string init = assert_op("(= "+SMVgetInit(context, out)+" "+zero+")");
      string trans_1 = "(=> (= (bvand " + SMVgetCurr(context, en) + "(bvand (bvnot " + SMVgetCurr(context, clk) + ") " + SMVgetNext(context, clk) + ")) #b1) (= " + SMVgetNext(context, out) + " (bvadd " + SMVgetCurr(context, out) + " " + one + ")))";
      string trans_2 = "(=> (not (= (bvand " + SMVgetCurr(context, en) + "(bvand (bvnot " + SMVgetCurr(context, clk) + ") " + SMVgetNext(context, clk) + ")) #b1)) (= " + SMVgetNext(context, out) + " " + SMVgetCurr(context, out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + init + NL + trans;
    }

    string SMVSlice(string context, SmvBVVar in_p, SmvBVVar out_p, string low, string high) {
      // INIT: TRUE
      // TRANS: (_ extract high low) in out) & (_ extract high low) in' out')
      string in = in_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMVSlice (in, out, low, high) = (" + in + ", " + out + ", " + low + ", " + high + ")";
      string op = "(_ extract " + high + " " + low + ")";
      string curr = unary_op_eqass(op, SMVgetCurr(context, in), SMVgetCurr(context, out));
      string next = unary_op_eqass(op, SMVgetNext(context, in), SMVgetNext(context, out));
      return comment + NL + curr + NL + next;
    }

    string SMVClock(string context, SmvBVVar clk_p) {
      // INIT: clk = 0
      // TRANS: (!clk & clk')
      string clk = clk_p.getPortName();
      string comment = ";; SMVClock (clk) = (" + clk + ")";
      string init = assert_op("(= #b0 "+SMVgetInit(context, clk)+")");
      string trans = assert_op("(= " + SMVgetCurr(context, clk) + " (bvnot " + SMVgetNext(context, clk) + "))");
      return comment + NL + init + NL + trans;
    }

  }
}
