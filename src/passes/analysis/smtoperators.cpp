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
    
    string SMTAssign(Connection con) {
      Wireable* left = con.first->getType()->getDir()==Type::DK_In ? con.first : con.second;
      Wireable* right = left==con.first ? con.second : con.first;
      SmtBVVar vleft(left);
      SmtBVVar vright(right);
      SmtBVVar vleft_c = SmtBVVarGetCurr(vleft);
      SmtBVVar vright_c = SmtBVVarGetCurr(vleft);
      SmtBVVar vleft_n = SmtBVVarGetNext(vleft);
      SmtBVVar vright_n = SmtBVVarGetNext(vleft);
      string curr = assert_op(binary_op("=", vleft_c.getName(), vright_c.getName()));
      string next = assert_op(binary_op("=", vleft_n.getName(), vright_n.getName()));
      return curr + NL + next;
    }

    string getVarName(named_var var) {
      return var.first+"_"+ var.second.getName();
    }
    
    string SMTAnd(named_var in1_p, named_var in2_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: ((in1 & in2) = out) & ((in1' & in2') = out')
      string in1 = getVarName(in1_p);
      string in2 = getVarName(in2_p);
      string out = getVarName(out_p);
      string comment = ";; SMTAnd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvand";
      string curr = binary_op_eqass(op, SMTgetCurr(in1), SMTgetCurr(in2), SMTgetCurr(out));
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTOr(named_var in1_p, named_var in2_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: ((in1 | in2) = out) & ((in1' | in2') = out')
      string in1 = getVarName(in1_p);
      string in2 = getVarName(in2_p);
      string out = getVarName(out_p);
      string comment = ";; SMTOr (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvor";
      string curr = binary_op_eqass(op, SMTgetCurr(in1), SMTgetCurr(in2), SMTgetCurr(out));
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTNot(named_var in_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: (!in = out) & (!in' = out')
      string in = getVarName(in_p);
      string out = getVarName(out_p);
      string comment = ";; SMTNot (in, out) = (" + in + ", " + out + ")";
      string op = "bvnot";
      string curr = unary_op_eqass(op, SMTgetCurr(in), SMTgetCurr(out));
      string next = unary_op_eqass(op, SMTgetNext(in), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTConst(named_var out_p, string val) {
      string out = getVarName(out_p);
      string comment = ";; SMTConst (out, val) = (" + out + ", " + val + ")";
      string curr = assert_op("(= " + SMTgetCurr(out) + " " + val + ")");
      string next = assert_op("(= " + SMTgetNext(out) + " " + val + ")");
      return comment + NL + curr + NL + next;
    }

    string SMTAdd(named_var in1_p, named_var in2_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: ((in1 + in2) = out) & ((in1' + in2') = out')
      string in1 = getVarName(in1_p);
      string in2 = getVarName(in2_p);
      string out = getVarName(out_p);
      string comment = ";; SMTAdd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvadd";
      string curr = binary_op_eqass(op, SMTgetCurr(in1), SMTgetCurr(in2), SMTgetCurr(out));
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTConcat(named_var in1_p, named_var in2_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: ((in1 concat in2) = out) & ((in1' concat in2') = out')
      string in1 = getVarName(in1_p);
      string in2 = getVarName(in2_p);
      string out = getVarName(out_p);
      string comment = ";; SMTConcat (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "concat";
      string curr = binary_op_eqass(op, SMTgetCurr(in1), SMTgetCurr(in2), SMTgetCurr(out));
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string SMTReg(named_var in_p, named_var clk_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: (!clk & clk') -> (out' = in)
      string in = getVarName(in_p);
      string clk = getVarName(clk_p);
      string out = getVarName(out_p);      
      string comment = ";; SMTReg (in, clk, out) = (" + in + ", " + clk + ", " + out + ")";
      return "(assert (=> (= (bvand (bvnot " + SMTgetCurr(clk) + ") " + SMTgetNext(clk) + ") #b1) (= " + SMTgetNext(out) + " " + SMTgetCurr(in) + ")))";
    }
    
    string SMTRegPE(named_var in_p, named_var clk_p, named_var out_p, named_var en_p) {
      // INIT: TRUE
      // TRANS: (en & !clk & clk') -> (out' = in)
      string in = getVarName(in_p);
      string clk = getVarName(clk_p);
      string out = getVarName(out_p);      
      string en = getVarName(en_p);
      string comment = ";; SMTRegPE (in, clk, out, en) = (" + in + ", " + clk + ", " + out + ", " + en + ")";
      string trans = "(assert (=> (= (bvand " + SMTgetCurr(en) + " (bvand (bvnot " + SMTgetCurr(clk) + ") " + SMTgetNext(clk) + ")) #b1) (= " + SMTgetNext(out) + " " + SMTgetCurr(in) + ")))";
      return comment + NL + trans;
    }

    string SMTCounter(named_var clk_p, named_var en_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: (en & !clk & clk') -> (out' = out+1)
      string clk = getVarName(clk_p);
      string out = getVarName(out_p);      
      string en = getVarName(en_p);
      string one = getSMTbits(stoi(out_p.second.dimstr()), 1);
      string comment = ";; SMTCounter (clk, en, out) = (" + clk + ", " + en + ", " + out + ")";
      string trans = "(assert (=> (= (bvand " + SMTgetCurr(en) + "(bvand (bvnot " + SMTgetCurr(clk) + ") " + SMTgetNext(clk) + ")) #b1) (= " + SMTgetNext(out) + " (bvadd " + SMTgetCurr(out) + " " + one + "))))";
      return comment + NL + trans;
    }
 
    string SMTSlice(named_var in_p, named_var out_p, string low, string high) {
      // INIT: TRUE
      // TRANS: (_ extract high low) in out) & (_ extract high low) in' out')
      string in = getVarName(in_p);
      string out = getVarName(out_p);      
      string comment = ";; SMTSlice (in, out, low, high) = (" + in + ", " + out + ", " + low + ", " + high + ")";
      string op = "(_ extract " + high + " " + low + ")";
      string curr = unary_op_eqass(op, SMTgetCurr(in), SMTgetCurr(out));
      string next = unary_op_eqass(op, SMTgetNext(in), SMTgetNext(out));
      return comment + NL + curr + NL + next;
    }
    
  }
}
