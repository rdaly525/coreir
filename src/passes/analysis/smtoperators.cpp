#include "coreir.h"
#include "coreir-passes/analysis/smtoperators.hpp"

using namespace CoreIR;

namespace CoreIR {
namespace Passes {

string NEXT_PF = "_N";
  
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
 
string SMTAnd(SmtBVVar in1, SmtBVVar in2, SmtBVVar out) {
  // (in1 & in2 = out) & (in1' & in2' = out')
  string op = "bvand";
  string current = binary_op(op, in1.getName(), in2.getName(), out.getName());
  string next = binary_op(op, SMTgetNext(in1.getName()), SMTgetNext(in2.getName()), SMTgetNext(out.getName()));
  return current + next;
}

string SMTOr(SmtBVVar in1, SmtBVVar in2, SmtBVVar out) {
  // (in1 | in2 = out) & (in1' | in2' = out')
  string op = "bvor";
  string current = binary_op(op, in1.getName(), in2.getName(), out.getName());
  string next = binary_op(op, SMTgetNext(in1.getName()), SMTgetNext(in2.getName()), SMTgetNext(out.getName()));
  return current + next;
}

string SMTNot(SmtBVVar in, SmtBVVar out) {
  // (!in = out) & (!in' = out')
  string op = "bvnot";
  string current = unary_op("op", in.getName(), out.getName());
  string next = unary_op("op", SMTgetNext(in.getName()), SMTgetNext(out.getName()));
  return current + next;
}

string SMTReg(SmtBVVar in, SmtBVVar clk, SmtBVVar out) {
  // (!clk & clk') -> (out' = in)
  return "(assert (=> ((bvand (bvnot " + clk.getName() + ") " + SMTgetNext(clk.getName()) + ")) (= " + SMTgetNext(out.getName()) + " " + in.getName() + ")))";
}

}
}
