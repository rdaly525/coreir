#include "coreir.h"
#include "coreir-passes/analysis/smtoperators.hpp"
#include <bitset>

using namespace CoreIR;

namespace CoreIR {
  namespace Passes {

    string NEXT_PF = "__NEXT__";
    string NL = "\n";
  
    string SMTgetNext(string var) {return var + NEXT_PF; }

    string getSMTbits(unsigned width, int x) {
      bitset<numeric_limits<int>::digits> b(x);
      return "0bin" + b.to_string().substr(numeric_limits<int>::digits - width);
    }

    string assert_op(string expr) {
      return "(assert "+ expr + "))";
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
      return "  (= " + vleft.getName() + " " + vright.getName() + ")";
    }
 
    string SMTAnd(string in1, string in2, string out) {
      // INIT: TRUE
      // TRANS: ((in1 & in2) = out) & ((in1' & in2') = out')
      string comment = ";; SMTAnd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvand";
      string current = binary_op_eqass(op, in1, in2, out);
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + current + NL + next;
    }

    string SMTOr(string in1, string in2, string out) {
      // INIT: TRUE
      // TRANS: ((in1 | in2) = out) & ((in1' | in2') = out')
      string comment = ";; SMTOr (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvor";
      string current = binary_op_eqass(op, in1, in2, out);
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + current + NL + next;
    }

    string SMTNot(string in, string out) {
      // INIT: TRUE
      // TRANS: (!in = out) & (!in' = out')
      string comment = ";; SMTNot (in, out) = (" + in + ", " + out + ")";
      string op = "bvnot";
      string current = unary_op_eqass(op, in, out);
      string next = unary_op_eqass(op, SMTgetNext(in), SMTgetNext(out));
      return comment + NL + current + NL + next;
    }

    string SMTConst(string out, string val) {
      string comment = ";; SMTConst (out, val) = (" + out + ", " + val + ")";
      string current = "(= " + out + " " + val + ")";
      string next = "(= " + SMTgetNext(out) + " " + val + ")";
      return comment + NL + current + NL + next;
    }

    string SMTAdd(string in1, string in2, string out) {
      // INIT: TRUE
      // TRANS: ((in1 + in2) = out) & ((in1' + in2') = out')
      string comment = ";; SMTAdd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvadd";
      string current = binary_op_eqass(op, in1, in2, out);
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + current + NL + next;
    }

    string SMTConcat(string in1, string in2, string out) {
      // INIT: TRUE
      // TRANS: ((in1 concat in2) = out) & ((in1' concat in2') = out')
      string comment = ";; SMTConcat (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "concat";
      string current = binary_op_eqass(op, in1, in2, out);
      string next = binary_op_eqass(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return comment + NL + current + NL + next;
    }

    string SMTReg(string in, string clk, string out) {
      // INIT: TRUE
      // TRANS: (!clk & clk') -> (out' = in)
      string comment = ";; SMTReg (in, clk, out) = (" + in + ", " + clk + ", " + out + ")";
      return "(assert (=> ((bvand (bvnot " + clk + ") " + SMTgetNext(clk) + ")) (= " + SMTgetNext(out) + " " + in + ")))";
    }
    
    string SMTRegPE(string in, string clk, string out, string en) {
      // INIT: TRUE
      // TRANS: (en & !clk & clk') -> (out' = in)
      string comment = ";; SMTRegPE (in, clk, out, en) = (" + in + ", " + clk + ", " + out + ", " + en + ")";
      string trans = "(assert (=> ((bvand " + en + " (bvand (bvnot " + clk + ") " + SMTgetNext(clk) + "))) (= " + SMTgetNext(out) + " " + in + ")))";
      return comment + NL + trans;
    }

    string SMTCounter(string clk, string en, string out) {
      // INIT: TRUE
      // TRANS: (en & !clk & clk') -> (out' = out+1)
      string comment = ";; SMTCounter (clk, en, out) = (" + clk + ", " + en + ", " + out + ")";
      string trans = "(assert (=> ((bvand " + en + "(bvand (bvnot " + clk + ") " + SMTgetNext(clk) + "))) (= " + SMTgetNext(out) + " (bvadd " + out + " 0x1))))";
      return comment + NL + trans;
    }

    string SMTSlice(string in, string out, string low, string high) {
      // INIT: TRUE
      // TRANS: (_ extract high low) in out) & (_ extract high low) in' out')
      string comment = ";; SMTSlice (in, out, low, high) = (" + in + ", " + out + ", " + low + ", " + high + ")";
      string op = "(_ extract " + high + " " + low + ")";
      string current = unary_op_eqass(op, in, out);
      string next = unary_op_eqass(op, SMTgetNext(in), SMTgetNext(out));
      return comment + NL + current + NL + next;
    }
    
  }
}
