#include "coreir.h"
#include "coreir/passes/analysis/smtoperators.hpp"
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

  string binary_op(string op, string in1, string in2) {
    return "(" + op + " " + in1 + " " + in2 + ")";
  }
}

namespace CoreIR {
  namespace Passes {

    string SMTgetInit(string context, string var) {return context + var + INIT_PF; }
    string SMTgetCurr(string context, string var) {return context + var + CURR_PF; }
    string SMTgetNext(string context, string var) {return context + var + NEXT_PF; }

    SmtBVVar SmtBVVarGetInit(SmtBVVar var) {
      var.setName(SMTgetInit("", var.getName()));
      return var;
    }

    SmtBVVar SmtBVVarGetNext(SmtBVVar var) {
      var.setName(SMTgetNext("", var.getName()));
      return var;
    }

    SmtBVVar SmtBVVarGetCurr(SmtBVVar var) {
      var.setName(SMTgetCurr("", var.getName()));
      return var;
    }

    string SmtBVVarDec(SmtBVVar w) {
      return "(declare-fun " + w.getName() + " () (_ BitVec " + w.dimstr() + "))";
    }

    string getSMTbits(unsigned width, int x) {
      bitset<numeric_limits<int>::digits> b(x);
      return "#b" + b.to_string().substr(numeric_limits<int>::digits - width);
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

    string SMTBop(string context, string opname, string op, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      // INIT: TRUE
      // TRANS: ((in1 <op> in2) = out) & ((in1' & in2') = out')
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMT" + opname + " (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string curr = binary_op_eqass(op, SMTgetCurr(context, in1), SMTgetCurr(context, in2), SMTgetCurr(context, out));
      string next = binary_op_eqass(op, SMTgetNext(context, in1), SMTgetNext(context, in2), SMTgetNext(context, out));
      return comment + NL + curr + NL + next;
    }
    
    string SMTAnd(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "And", "bvand", in1_p, in2_p, out_p);
    }

    string SMTOr(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "Or", "bvor", in1_p, in2_p, out_p);
    }

    string SMTXor(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "Xor", "bvxor", in1_p, in2_p, out_p);
    }
    
    string SMTAdd(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "Add", "bvadd", in1_p, in2_p, out_p);
    }

    string SMTConcat(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "Concat", "concat", in1_p, in2_p, out_p);
    }

    string SMTUop(string context, string opname, string op, SmtBVVar in_p, SmtBVVar out_p) {
      // INIT: TRUE
      // TRANS: (in <op> out) & (in' <op> out')
      string in = in_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMT" + opname + " (in, out) = (" + in + ", " + out + ")";
      string curr = unary_op_eqass(op, SMTgetCurr(context, in), SMTgetCurr(context, out));
      string next = unary_op_eqass(op, SMTgetNext(context, in), SMTgetNext(context, out));
      return comment + NL + curr + NL + next;
    }
    
    string SMTSlice(string context, SmtBVVar in_p, SmtBVVar out_p, int low_p, int high_p) {
      string low = to_string(low_p);
      string high = to_string(high_p);      
      string op = "(_ extract " + high + " " + low + ")";
      return SMTUop(context, "Slice", op, in_p, out_p);
    }
    
    string SMTNot(string context, SmtBVVar in_p, SmtBVVar out_p) {
      return SMTUop(context, "Not", "bvnot", in_p, out_p);
    }

    string SMTConst(string context, SmtBVVar out_p, string val) {
      string out = out_p.getPortName();
      string comment = ";; SMTConst (out, val) = (" + out + ", " + val + ")";
      string curr = assert_op("(= " + SMTgetCurr(context, out) + " " + val + ")");
      string next = assert_op("(= " + SMTgetNext(context, out) + " " + val + ")");
      return comment + NL + curr + NL + next;
    }
    
    string SMTReg(string context, SmtBVVar in_p, SmtBVVar clk_p, SmtBVVar out_p) {
      // INIT: out = 0
      // TRANS: ((!clk & clk') -> (out' = in)) & (!(!clk & clk') -> (out' = out))
      string in = in_p.getPortName();
      string clk = clk_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMTReg (in, clk, out) = (" + in + ", " + clk + ", " + out + ")";
      string zero = getSMTbits(stoi(out_p.dimstr()), 0);
      string init = assert_op("(= "+SMTgetInit(context, out)+" "+zero+")");
      string trans_1 = "(=> (= (bvand (bvnot " + SMTgetCurr(context, clk) + ") " + SMTgetNext(context, clk) + ") #b1) (= " + SMTgetNext(context, out) + " " + SMTgetCurr(context, in) + "))";
      string trans_2 = "(=> (not (= (bvand (bvnot " + SMTgetCurr(context, clk) + ") " + SMTgetNext(context, clk) + ") #b1)) (= " + SMTgetNext(context, out) + " " + SMTgetCurr(context, out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + init + NL + trans;
    }

    string SMTRegPE(string context, SmtBVVar in_p, SmtBVVar clk_p, SmtBVVar out_p, SmtBVVar en_p) {
      // INIT: out = 0
      // TRANS: ((en & !clk & clk') -> (out' = in)) & (!(en & !clk & clk') -> (out' = out))
      string in = in_p.getPortName();
      string clk = clk_p.getPortName();
      string out = out_p.getPortName();
      string en = en_p.getPortName();
      string comment = ";; SMTRegPE (in, clk, out, en) = (" + in + ", " + clk + ", " + out + ", " + en + ")";
      string zero = getSMTbits(stoi(out_p.dimstr()), 0);
      string init = assert_op("(= "+SMTgetInit(context, out)+" "+zero+")");
      string trans_1 = "(=> (= (bvand " + SMTgetCurr(context, en) + " (bvand (bvnot " + SMTgetCurr(context, clk) + ") " + SMTgetNext(context, clk) + ")) #b1) (= " + SMTgetNext(context, out) + " " + SMTgetCurr(context, in) + "))";
      string trans_2 = "(=> (not (= (bvand " + SMTgetCurr(context, en) + " (bvand (bvnot " + SMTgetCurr(context, clk) + ") " + SMTgetNext(context, clk) + ")) #b1)) (= " + SMTgetNext(context, out) + " " + SMTgetCurr(context, out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + init + NL + trans;
    }

    string SMTClock(string context, SmtBVVar clk_p) {
      // INIT: clk = 0
      // TRANS: (!clk & clk')
      string clk = clk_p.getPortName();
      string comment = ";; SMTClock (clk) = (" + clk + ")";
      string init = assert_op("(= #b0 "+SMTgetInit(context, clk)+")");
      string trans = assert_op("(= " + SMTgetCurr(context, clk) + " (bvnot " + SMTgetNext(context, clk) + "))");
      return comment + NL + init + NL + trans;
    }

  }
}
