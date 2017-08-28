#include "coreir.h"
#include "coreir-passes/analysis/smvoperators.hpp"
#include <bitset>

using namespace CoreIR;

namespace {
  string NL = "\n";


  string assert_op(string expr) {
    return "(assert "+ expr + ")";
  }

  string unary_op(string op, string in) {
    return "(" + op + " " + in + ")";
  }

  string binary_op(string op, string in1, string in2) {
    return "(" + in1 + " " + op + " " + in2 + ")";
  }
  
  string unary_op_eq(string op, string in, string out) {
    return binary_op("=", unary_op(op, in), out);
  }

  string binary_op_eq(string op, string in1, string in2, string out) {
    return binary_op("=", binary_op(op, in1, in2), out);
  }

  string get_init(string init) {
    return "INIT"+ NL + init + ";";
  }
  
  string get_trans(string trans) {
    return "TRANS"+ NL + trans + ";";
  }

  string get_invar(string invar) {
    return "INVAR"+ NL + invar + ";";
  }
  
}

namespace CoreIR {
  namespace Passes {

    string SMVgetCurr(string context, string var) {return context + var; }
    string SMVgetNext(string context, string var) {return "next(" + context + var + ")"; }

    SmvBVVar SmvBVVarGetNext(SmvBVVar var) {
      var.setName(SMVgetNext("", var.getName()));
      return var;
    }

    SmvBVVar SmvBVVarGetCurr(SmvBVVar var) {
      var.setName(SMVgetCurr("", var.getName()));
      return var;
    }

    string SmvBVVarDec(SmvBVVar w) {
      //      return "(declare-fun " + w.getName() + " () (_ BitVec " + w.dimstr() + "))";
      return "VAR " + w.getName() + ": word[" + w.dimstr() + "];";
    }

    string getSMVbits(unsigned width, int x) {
      bitset<numeric_limits<int>::digits> b(x);
      int wint = width;
      return "0ud"+(to_string(wint))+"_" + to_string(x);
    }

    string SMVAssign(SmvBVVar vleft, SmvBVVar vright) {
      SmvBVVar vleft_c = SmvBVVarGetCurr(vleft);
      SmvBVVar vright_c = SmvBVVarGetCurr(vright);
      SmvBVVar vleft_n = SmvBVVarGetNext(vleft);
      SmvBVVar vright_n = SmvBVVarGetNext(vright);
      string curr = binary_op("=", vleft_c.getExtractName(), vright_c.getExtractName());
      return get_invar(curr);
    }

    string SMVAnd(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 & in2) = out) & ((in1' & in2') = out')
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMVAnd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "&";
      string curr = binary_op_eq(op, SMVgetCurr(context, in1), SMVgetCurr(context, in2), SMVgetCurr(context, out));
      return comment + NL + get_invar(curr);
    }

    string SMVOr(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 | in2) = out) & ((in1' | in2') = out')
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMVOr (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "|";
      string curr = binary_op_eq(op, SMVgetCurr(context, in1), SMVgetCurr(context, in2), SMVgetCurr(context, out));
      return comment + NL + get_invar(curr);
    }

    string SMVNot(string context, SmvBVVar in_p, SmvBVVar out_p) {
      // INIT: TRUE
      // TRANS: (!in = out) & (!in' = out')
      string in = in_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMVNot (in, out) = (" + in + ", " + out + ")";
      string op = "!";
      string curr = unary_op_eq(op, SMVgetCurr(context, in), SMVgetCurr(context, out));
      return comment + NL + get_invar(curr);
    }

    string SMVConst(string context, SmvBVVar out_p, string val) {
      string out = out_p.getPortName();
      string comment = "-- SMVConst (out, val) = (" + out + ", " + val + ")";
      string curr = binary_op("=", SMVgetCurr(context, out), val);
      return comment + NL + get_invar(curr);
    }

    string SMVAdd(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 + in2) = out) & ((in1' + in2') = out')
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMVAdd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "+";
      string curr = binary_op_eq(op, SMVgetCurr(context, in1), SMVgetCurr(context, in2), SMVgetCurr(context, out));
      return comment + NL + get_invar(curr);
    }

    string SMVConcat(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 concat in2) = out) & ((in1' concat in2') = out')
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMVConcat (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "::";
      string curr = binary_op_eq(op, SMVgetCurr(context, in1), SMVgetCurr(context, in2), SMVgetCurr(context, out));
      return comment + NL + get_invar(curr);
    }

    string SMVReg(string context, SmvBVVar in_p, SmvBVVar clk_p, SmvBVVar out_p) {
      // INIT: out = 0
      // TRANS: ((!clk & clk') -> (out' = in)) & (!(!clk & clk') -> (out' = out))
      string in = in_p.getPortName();
      string clk = clk_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMVReg (in, clk, out) = (" + in + ", " + clk + ", " + out + ")";
      string zero = getSMVbits(stoi(out_p.dimstr()), 0);
      string init = binary_op("=", SMVgetCurr(context, out), zero);
      string trans_1 = "(((!"+SMVgetCurr(context, clk)+" & next("+SMVgetCurr(context, clk)+")) = 0ud1_1) -> (next("+SMVgetCurr(context, out)+") = "+SMVgetCurr(context, in)+"))";
      string trans_2 = "((!(!"+SMVgetCurr(context, clk)+" & next("+SMVgetCurr(context, clk)+")) = 0ud1_1) -> (next("+SMVgetCurr(context, out)+") = "+SMVgetCurr(context, out)+"))";
      string trans = binary_op("&", trans_1, trans_2);
      return comment + NL + get_init(init) + NL + get_trans(trans);
    }

    string SMVRegPE(string context, SmvBVVar in_p, SmvBVVar clk_p, SmvBVVar out_p, SmvBVVar en_p) {
      // INIT: out = 0
      // TRANS: ((en & !clk & clk') -> (out' = in)) & (!(en & !clk & clk') -> (out' = out))
      string in = in_p.getPortName();
      string clk = clk_p.getPortName();
      string out = out_p.getPortName();
      string en = en_p.getPortName();
      string comment = "-- SMVRegPE (in, clk, out, en) = (" + in + ", " + clk + ", " + out + ", " + en + ")";
      string zero = getSMVbits(stoi(out_p.dimstr()), 0);
      string init = binary_op("=", SMVgetCurr(context, out), zero);
      string trans_1 = "((("+SMVgetCurr(context, en)+" & !"+SMVgetCurr(context, clk)+" & next("+SMVgetCurr(context, clk)+")) = 0ud1_1) -> (next("+SMVgetCurr(context, out)+") = "+SMVgetCurr(context, in)+"))";
      string trans_2 = "((!("+SMVgetCurr(context, en)+" & !"+SMVgetCurr(context, clk)+" & next("+SMVgetCurr(context, clk)+")) = 0ud1_1) -> (next("+SMVgetCurr(context, out)+") = "+SMVgetCurr(context, out)+"))";
      string trans = binary_op("&", trans_1, trans_2);
      return comment + NL + get_init(init) + NL + get_trans(trans);
    }

    string SMVSlice(string context, SmvBVVar in_p, SmvBVVar out_p, string low, string high) {
      // INIT: TRUE
      // TRANS: (_ extract high low) in out) & (_ extract high low) in' out')
      string in = in_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMVSlice (in, out, low, high) = (" + in + ", " + out + ", " + low + ", " + high + ")";
      string op = "[" + high + ":" + low + "]";
      string curr = SMVgetCurr(context, in) + op + "=" + SMVgetCurr(context, out);
      return comment + NL + get_invar(curr);
    }

    string SMVClock(string context, SmvBVVar clk_p) {
      // INIT: clk = 0
      // TRANS: (!clk & clk')
      string clk = clk_p.getPortName();
      string comment = "-- SMVClock (clk) = (" + clk + ")";
      string init = binary_op("=", "0ud1_0", SMVgetCurr(context, clk));
      string trans = binary_op("=", SMVgetCurr(context, clk), unary_op("!", SMVgetNext(context, clk)));
      return comment + NL + get_init(init) + NL + get_trans(trans);
    }

  }
}
