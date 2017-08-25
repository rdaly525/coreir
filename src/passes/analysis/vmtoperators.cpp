#include "coreir.h"
#include "coreir-passes/analysis/vmtoperators.hpp"
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
  
    string VMTgetInit(string var) {return var + INIT_PF; }
    string VMTgetCurr(string var) {return var + CURR_PF; }
    string VMTgetNext(string var) {return var + NEXT_PF; }

    VmtBVVar VmtBVVarGetInit(VmtBVVar var) {
      var.setName(VMTgetInit(var.getName()));
      return var;
    }
    
    VmtBVVar VmtBVVarGetNext(VmtBVVar var) {
      var.setName(VMTgetNext(var.getName()));
      return var;
    }

    VmtBVVar VmtBVVarGetCurr(VmtBVVar var) {
      var.setName(VMTgetCurr(var.getName()));
      return var;
    }

    string VmtBVVarDec(VmtBVVar w) {
      return "(declare-fun " + w.getName() + " () (_ BitVec " + w.dimstr() + "))";
    }
    
    string getVMTbits(unsigned width, int x) {
      bitset<numeric_limits<int>::digits> b(x);
      return "#b" + b.to_string().substr(numeric_limits<int>::digits - width);
    }
    
    string VMTAssign(VmtBVVar vleft, VmtBVVar vright) {
      VmtBVVar vleft_c = VmtBVVarGetCurr(vleft);
      VmtBVVar vright_c = VmtBVVarGetCurr(vright);
      VmtBVVar vleft_n = VmtBVVarGetNext(vleft);
      VmtBVVar vright_n = VmtBVVarGetNext(vright);
      string curr = assert_op(binary_op("=", vleft_c.getExtractName(), vright_c.getExtractName()));
      string next = assert_op(binary_op("=", vleft_n.getExtractName(), vright_n.getExtractName()));
      return curr + NL + next;
    }

    string getVarName(named_var var) {
      return (var.first == "" ? "" : var.first + "_") + var.second.getName();
    }
    
    string VMTAnd(named_var in1_p, named_var in2_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: ((in1 & in2) = out) & ((in1' & in2') = out')
      string in1 = getVarName(in1_p);
      string in2 = getVarName(in2_p);
      string out = getVarName(out_p);
      string comment = ";; VMTAnd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvand";
      string curr = binary_op_eqass(op, VMTgetCurr(in1), VMTgetCurr(in2), VMTgetCurr(out));
      string next = binary_op_eqass(op, VMTgetNext(in1), VMTgetNext(in2), VMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string VMTOr(named_var in1_p, named_var in2_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: ((in1 | in2) = out) & ((in1' | in2') = out')
      string in1 = getVarName(in1_p);
      string in2 = getVarName(in2_p);
      string out = getVarName(out_p);
      string comment = ";; VMTOr (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvor";
      string curr = binary_op_eqass(op, VMTgetCurr(in1), VMTgetCurr(in2), VMTgetCurr(out));
      string next = binary_op_eqass(op, VMTgetNext(in1), VMTgetNext(in2), VMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string VMTNot(named_var in_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: (!in = out) & (!in' = out')
      string in = getVarName(in_p);
      string out = getVarName(out_p);
      string comment = ";; VMTNot (in, out) = (" + in + ", " + out + ")";
      string op = "bvnot";
      string curr = unary_op_eqass(op, VMTgetCurr(in), VMTgetCurr(out));
      string next = unary_op_eqass(op, VMTgetNext(in), VMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string VMTConst(named_var out_p, string val) {
      string out = getVarName(out_p);
      string comment = ";; VMTConst (out, val) = (" + out + ", " + val + ")";
      string curr = assert_op("(= " + VMTgetCurr(out) + " " + val + ")");
      string next = assert_op("(= " + VMTgetNext(out) + " " + val + ")");
      return comment + NL + curr + NL + next;
    }

    string VMTAdd(named_var in1_p, named_var in2_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: ((in1 + in2) = out) & ((in1' + in2') = out')
      string in1 = getVarName(in1_p);
      string in2 = getVarName(in2_p);
      string out = getVarName(out_p);
      string comment = ";; VMTAdd (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "bvadd";
      string curr = binary_op_eqass(op, VMTgetCurr(in1), VMTgetCurr(in2), VMTgetCurr(out));
      string next = binary_op_eqass(op, VMTgetNext(in1), VMTgetNext(in2), VMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string VMTConcat(named_var in1_p, named_var in2_p, named_var out_p) {
      // INIT: TRUE
      // TRANS: ((in1 concat in2) = out) & ((in1' concat in2') = out')
      string in1 = getVarName(in1_p);
      string in2 = getVarName(in2_p);
      string out = getVarName(out_p);
      string comment = ";; VMTConcat (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string op = "concat";
      string curr = binary_op_eqass(op, VMTgetCurr(in1), VMTgetCurr(in2), VMTgetCurr(out));
      string next = binary_op_eqass(op, VMTgetNext(in1), VMTgetNext(in2), VMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string VMTReg(named_var in_p, named_var clk_p, named_var out_p) {
      // INIT: out = 0
      // TRANS: ((!clk & clk') -> (out' = in)) & (!(!clk & clk') -> (out' = out))
      string in = getVarName(in_p);
      string clk = getVarName(clk_p);
      string out = getVarName(out_p);      
      string comment = ";; VMTReg (in, clk, out) = (" + in + ", " + clk + ", " + out + ")";
      string zero = getVMTbits(stoi(out_p.second.dimstr()), 0);
      string init = assert_op("(= "+VMTgetInit(out)+" "+zero+")");
      string trans_1 = "(=> (= (bvand (bvnot " + VMTgetCurr(clk) + ") " + VMTgetNext(clk) + ") #b1) (= " + VMTgetNext(out) + " " + VMTgetCurr(in) + "))";
      string trans_2 = "(=> (not (= (bvand (bvnot " + VMTgetCurr(clk) + ") " + VMTgetNext(clk) + ") #b1)) (= " + VMTgetNext(out) + " " + VMTgetCurr(out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + init + NL + trans;
    }
    
    string VMTRegPE(named_var in_p, named_var clk_p, named_var out_p, named_var en_p) {
      // INIT: out = 0
      // TRANS: ((en & !clk & clk') -> (out' = in)) & (!(en & !clk & clk') -> (out' = out))
      string in = getVarName(in_p);
      string clk = getVarName(clk_p);
      string out = getVarName(out_p);      
      string en = getVarName(en_p);
      string zero = getVMTbits(stoi(out_p.second.dimstr()), 0);
      string comment = ";; VMTRegPE (in, clk, out, en) = (" + in + ", " + clk + ", " + out + ", " + en + ")";
      string init = assert_op("(= "+VMTgetInit(out)+" "+zero+")");
      string trans_1 = "(=> (= (bvand " + VMTgetCurr(en) + " (bvand (bvnot " + VMTgetCurr(clk) + ") " + VMTgetNext(clk) + ")) #b1) (= " + VMTgetNext(out) + " " + VMTgetCurr(in) + "))";
      string trans_2 = "(=> (not (= (bvand " + VMTgetCurr(en) + " (bvand (bvnot " + VMTgetCurr(clk) + ") " + VMTgetNext(clk) + ")) #b1)) (= " + VMTgetNext(out) + " " + VMTgetCurr(out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + init + NL + trans;
    }

    string VMTCounter(named_var clk_p, named_var en_p, named_var out_p) {
      // INIT: out = 0
      // TRANS: ((en & !clk & clk') -> (out' = out+1)) & (!(en & !clk & clk') -> (out' = out))
      string clk = getVarName(clk_p);
      string out = getVarName(out_p);      
      string en = getVarName(en_p);
      string zero = getVMTbits(stoi(out_p.second.dimstr()), 0);
      string one = getVMTbits(stoi(out_p.second.dimstr()), 1);
      string comment = ";; VMTCounter (clk, en, out) = (" + clk + ", " + en + ", " + out + ")";
      string init = assert_op("(= "+VMTgetInit(out)+" "+zero+")");
      string trans_1 = "(=> (= (bvand " + VMTgetCurr(en) + "(bvand (bvnot " + VMTgetCurr(clk) + ") " + VMTgetNext(clk) + ")) #b1) (= " + VMTgetNext(out) + " (bvadd " + VMTgetCurr(out) + " " + one + ")))";
      string trans_2 = "(=> (not (= (bvand " + VMTgetCurr(en) + "(bvand (bvnot " + VMTgetCurr(clk) + ") " + VMTgetNext(clk) + ")) #b1)) (= " + VMTgetNext(out) + " " + VMTgetCurr(out) + "))";
      string trans = assert_op("(and " + trans_1 + " " + trans_2 + ")");
      return comment + NL + init + NL + trans;
    }
 
    string VMTSlice(named_var in_p, named_var out_p, string low, string high) {
      // INIT: TRUE
      // TRANS: (_ extract high low) in out) & (_ extract high low) in' out')
      string in = getVarName(in_p);
      string out = getVarName(out_p);      
      string comment = ";; VMTSlice (in, out, low, high) = (" + in + ", " + out + ", " + low + ", " + high + ")";
      string op = "(_ extract " + high + " " + low + ")";
      string curr = unary_op_eqass(op, VMTgetCurr(in), VMTgetCurr(out));
      string next = unary_op_eqass(op, VMTgetNext(in), VMTgetNext(out));
      return comment + NL + curr + NL + next;
    }

    string VMTClock(named_var clk_p) {
      // INIT: clk = 0
      // TRANS: (!clk & clk')
      string clk = getVarName(clk_p);
      string comment = ";; VMTClock (clk) = (" + clk + ")";
      string init = assert_op("(= #b0 "+VMTgetInit(clk)+")");
      string trans = assert_op("(= " + VMTgetCurr(clk) + " (bvnot " + VMTgetNext(clk) + "))");
      return comment + NL + init + NL + trans;
    }
    
  }
}
