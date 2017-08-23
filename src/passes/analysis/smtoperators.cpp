#include "coreir.h"
#include "coreir-passes/analysis/smtoperators.hpp"

using namespace CoreIR;

namespace CoreIR {
  namespace Passes {

    string NEXT_PF = "__NEXT__";
    string NL = "\n";
  
    string SMTgetNext(string var) {return var + NEXT_PF; }

    string unary_op(string op, string in, string out) {
      return "(assert (= (" + op + " " + in + ") " + out + "))";
    }
  
    string binary_op(string op, string in1, string in2, string out) {
      return "(assert (= (" + op + " " + in1 + " " + in2 + ") " + out + "))";
    }
 
    string SMTAssign(Connection con) {
      Wireable* left = con.first->getType()->getDir()==Type::DK_In ? con.first : con.second;
      Wireable* right = left==con.first ? con.second : con.first;
      SmtBVVar vleft(left);
      SmtBVVar vright(right);
      return "  (= " + vleft.getName() + " " + vright.getName() + ")";
    }
 
    string SMTAnd(string in1, string in2, string out) {
      // (in1 & in2 = out) & (in1' & in2' = out')
      string op = "bvand";
      string current = binary_op(op, in1, in2, out);
      string next = binary_op(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return current + next;
    }

    string SMTOr(string in1, string in2, string out) {
      // (in1 | in2 = out) & (in1' | in2' = out')
      string op = "bvor";
      string current = binary_op(op, in1, in2, out);
      string next = binary_op(op, SMTgetNext(in1), SMTgetNext(in2), SMTgetNext(out));
      return current + next;
    }

    string SMTNot(string in, string out) {
      // (!in = out) & (!in' = out')
      string op = "bvnot";
      string current = unary_op(op, in, out);
      string next = unary_op(op, SMTgetNext(in), SMTgetNext(out));
      return current + NL + next;
    }

    string SMTReg(string in, string clk, string out) {
      // (!clk & clk') -> (out' = in)
      return "(assert (=> ((bvand (bvnot " + clk + ") " + SMTgetNext(clk) + ")) (= " + SMTgetNext(out) + " " + in + ")))";
    }

    string SMTConst(string out) {
      string op = "=";
      string val = "0x0";
      string current = unary_op(op, val, out);
      string next = unary_op(op, val, SMTgetNext(out));
      return current + NL + next;
    }
    
  }
}
