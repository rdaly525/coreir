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
      bitset<256> b(x);
      return "#b" + b.to_string().substr(256 - width);
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

    string SMTEq(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      // INIT: TRUE
      // TRANS: (((in1 = in2) -> (out = #b1)) & ((in1 != in2) -> (out = #b0)))
      //        (((in1' = in2') -> (out' = #b1)) & ((in1' != in2') -> (out' = #b0)))
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMT Eq(in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";

      string input1;
      string input2;
      string output;

      input1 = SMTgetCurr(context, in1);
      input2 = SMTgetCurr(context, in2);
      output = SMTgetCurr(context, out);
      
      string curr = "(and (=> (= " + input1 + " " + input2 + ") (= " + output + " #b1)) "
                         "(=> (not (= " + input1 + " " + input2 + ")) (= " + output + " #b0)))";

      curr = "(assert " + curr + ")";
      
      input1 = SMTgetNext(context, in1);
      input2 = SMTgetNext(context, in2);
      output = SMTgetNext(context, out);
      
      string next = "(and (=> (= " + input1 + " " + input2 + ") (= " + output + " #b1)) "
                         "(=> (not (= " + input1 + " " + input2 + ")) (= " + output + " #b0)))";
      
      next = "(assert " + next + ")";
      
      return comment + NL + curr + NL + next;
    }
    
    string SMTXor(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "Xor", "bvxor", in1_p, in2_p, out_p);
    }

    string SMTAdd(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "Add", "bvadd", in1_p, in2_p, out_p);
    }

    string SMTSub(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "Sub", "bvsub", in1_p, in2_p, out_p);
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
      string vals;

      if (val == "False") {
        vals = getSMTbits(1, 1);
      }
      else if (val == "True") {
        vals = getSMTbits(1, 1);
      }
      else {
        try {
          vals = getSMTbits(stoi(out_p.dimstr()), stoi(val));
        }
        catch (std::invalid_argument& e){
          std::cerr << e.what() << std::endl;
        }
      }

      string comment = ";; SMTConst (out, val) = (" + out + ", " + vals + ")";
      string curr = assert_op("(= " + SMTgetCurr(context, out) + " " + vals + ")");
      string next = assert_op("(= " + SMTgetNext(context, out) + " " + vals + ")");
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

    // TODO: Translate Mantle Reg
    // Need parameters for CLR, CE and RESET
    //string SMTMantleReg
    string SMTMantleReg(string context, Values args, SmtBVVar I_p, SmtBVVar O_p, SmtBVVar CLK_p, SmtBVVar CLR_p, SmtBVVar CE_p, SmtBVVar RESET_p) {
      // INIT: out = modargs:init:val
      int width = stoi(args["width"]->toString());
      string I = I_p.getPortName();
      string O = O_p.getPortName();
      string CLK = CLK_p.getPortName();
      string comment = ";; SMTMantleReg (I, O, CLK, CLR?, CE?, RESET?) = (" +
        I + ", " + O + ", " + CLK + ", " + args["has_clr"]->toString() +
        ", " + args["has_en"]->toString() + ", " +
        args["has_rst"]->toString() + ")";

      bool has_clr = args["has_clr"]->toString() == "True";
      bool has_ce = args["has_en"]->toString() == "True";
      bool has_rst = args["has_rst"]->toString() == "True";

      string clkToggle = "(and (= " + SMTgetCurr(context, CLK) + " #b0) (= " +
        SMTgetNext(context, CLK) + " #b1))";
      string initval = getSMTbits(width, stoi(args["init"]->toString()));
      string init = assert_op("(= " + SMTgetInit(context, O) + " " +
                              initval + ")");

      string trans;
      if (has_ce && has_rst) {
        string rst = "(= " + SMTgetCurr(context, RESET_p.getPortName()) + " #b1)";
        string ce = "(= " + SMTgetCurr(context, CE_p.getPortName()) + " #b1)";
        string trans1 = "(=> (and " + rst + " " + clkToggle + ") (= " +
          SMTgetNext(context, O) + " " + initval + "))";
        string trans2 = "(=> (and (not " + rst + ") " + clkToggle + " " +
          ce + ") (= " + SMTgetNext(context, O) + " " +
          SMTgetCurr(context, I) + "))";
        string trans3 = "(=> (or (and (not " + rst + ") (not " + ce + ")) (not " +
          clkToggle + ")) (= " + SMTgetNext(context, O) + " " + SMTgetCurr(context, O) + "))";
        trans = assert_op("(and " + trans1 + " " + trans2 + " " + trans3 + ")");
      }
      else if (has_ce) {
        string ce = "(= " + SMTgetCurr(context, CE_p.getPortName()) + " #b1)";
        string trans1 = "(=> (and " + ce + " " + clkToggle + ") (= " +
          SMTgetNext(context, O) + " " + SMTgetCurr(context, I) + "))";
        string trans2 = "(=> (or (not " + ce + ") (not " + clkToggle + "))"
          "(= " + SMTgetNext(context, O) + " " + SMTgetCurr(context, O) + "))";
        trans = assert_op("(and " + trans1 + " " + trans2 + ")");
      }
      else if (has_rst) {
        string rst = "(= " + SMTgetCurr(context, RESET_p.getPortName()) + " #b1)";
        string trans1 = "(=> (and " + rst + " " + clkToggle + ") (= " +
          SMTgetNext(context, O) + " " + initval + "))";
        string trans2 = "(=> (and (not " + rst + ") " + clkToggle + ") (= " +
          SMTgetNext(context, O) + " " + SMTgetCurr(context, I) + "))";
        string trans3 = "(=> (or (not " + rst + ") (not " + clkToggle + "))"
          "(= " + SMTgetNext(context, O) + " " + SMTgetCurr(context, O) + "))";
        trans = assert_op("(and " + trans1 + " " + trans2 + " " + trans3 + ")");
      }
      else {
        string trans1 = "(=> " + clkToggle + " " + "(= " +
          SMTgetNext(context, O) + " " + SMTgetCurr(context, I) + "))";
        string trans2 = "(=> (not " + clkToggle + ") " + "(= " +
          SMTgetNext(context, O) + " " + SMTgetCurr(context, O) + "))";
        trans = assert_op("(and " + trans1 + " " + trans2 + ")");
      }

      ASSERT(!has_clr, "CLR not supported by SMT translation yet.");
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

    string SMTMux(string context, SmtBVVar in0_p, SmtBVVar in1_p, SmtBVVar sel_p, SmtBVVar out_p) {
      string in0 = in0_p.getPortName();
      string in1 = in1_p.getPortName();
      string sel = sel_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMTMux (in0, in1, sel, out) = (" + in0 + ", " + in1 + ", " + sel + ", " + out + ")";

      string one = getSMTbits(stoi(sel_p.dimstr()), 1);
      string zero = getSMTbits(stoi(sel_p.dimstr()), 0);

      string then_bc = "(= "+SMTgetCurr(context, sel)+" "+one+")";
      string else_bc = "(= "+SMTgetCurr(context, sel)+" "+zero+")";
      string curr_1 = "(=> "+then_bc+" (= "+SMTgetCurr(context, in1)+" "+SMTgetCurr(context, out)+"))";
      string curr_2 = "(=> "+else_bc+" (= "+SMTgetCurr(context, in0)+" "+SMTgetCurr(context, out)+"))";
      string curr = assert_op("(and " + curr_1 + " " + curr_2 + ")");

      string then_bn = "(= "+SMTgetNext(context, sel)+" "+one+")";
      string else_bn = "(= "+SMTgetNext(context, sel)+" "+zero+")";
      string next_1 = "(=> "+then_bn+" (= "+SMTgetNext(context, in1)+" "+SMTgetNext(context, out)+"))";
      string next_2 = "(=> "+else_bn+" (= "+SMTgetNext(context, in0)+" "+SMTgetNext(context, out)+"))";
      string next = assert_op("(and " + next_1 + " " + next_2 + ")");

      return comment + NL + curr + NL + next;
    }

    string SMTLshr(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "Lshr", "bvlshr", in1_p, in2_p, out_p);
    }

    string SMTAshr(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "Ashr", "bvashr", in1_p, in2_p, out_p);
    }
    
    string SMTMul(string context, SmtBVVar in1_p, SmtBVVar in2_p, SmtBVVar out_p) {
      return SMTBop(context, "Mul", "bvmul", in1_p, in2_p, out_p);
    }

    string SMTAndr(string context, SmtBVVar in_p, SmtBVVar out_p) {
      string in = in_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMTAndr (in, out) = (" + in + ", " + out + ")";

      string one = getSMTbits(stoi(in_p.dimstr()), -1);

      string true_res; 
      string false_res;
      
      true_res  = "(=> (= "+SMTgetCurr(context, in)+" "+one+") ("+SMTgetCurr(context, out)+" #b1))";
      false_res = "(=> (not (= "+SMTgetCurr(context, in)+" "+one+")) ("+SMTgetCurr(context, out)+" #b0))";
      string curr = assert_op("(and "+true_res+" "+false_res+")");

      true_res  = "(=> (= "+SMTgetNext(context, in)+" "+one+") ("+SMTgetNext(context, out)+" #b1))";
      false_res = "(=> (not (= "+SMTgetNext(context, in)+" "+one+")) ("+SMTgetNext(context, out)+" #b0))";
      string next = assert_op("(and "+true_res+" "+false_res+")");
      
      return comment + NL + curr + NL + next;
    }

    string SMTOrr(string context, SmtBVVar in_p, SmtBVVar out_p) {
      string in = in_p.getPortName();
      string out = out_p.getPortName();
      string comment = ";; SMTOrr (in, out) = (" + in + ", " + out + ")";

      string zero = getSMTbits(stoi(in_p.dimstr()), 0);

      string true_res; 
      string false_res;
      
      true_res  = "(=> (= "+SMTgetCurr(context, in)+" "+zero+") ("+SMTgetCurr(context, out)+" #b0))";
      false_res = "(=> (not (= "+SMTgetCurr(context, in)+" "+zero+")) ("+SMTgetCurr(context, out)+" #b1))";
      string curr = assert_op("(and "+true_res+" "+false_res+")");

      true_res  = "(=> (= "+SMTgetNext(context, in)+" "+zero+") ("+SMTgetNext(context, out)+" #b0))";
      false_res = "(=> (not (= "+SMTgetNext(context, in)+" "+zero+")) ("+SMTgetNext(context, out)+" #b1))";
      string next = assert_op("(and "+true_res+" "+false_res+")");
      
      return comment + NL + curr + NL + next;
    }

    string SMTZext(string context, SmtBVVar in_p, SmtBVVar out_p) {
      return SMTUop(context, "Zext", "(_ zero_extend 1)", in_p, out_p);
    }
    
  }
}
