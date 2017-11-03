#include "coreir.h"
#include "coreir/passes/analysis/smvoperators.hpp"
#include <bitset>
#include <algorithm>

using namespace CoreIR;

namespace {
  string NL = "\n";

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
  
  void findAndReplaceAll(std::string & data, std::string toSearch, std::string replaceStr)
  {
    size_t pos = data.find(toSearch);
    while( pos != std::string::npos)
      {
        data.replace(pos, toSearch.size(), replaceStr);
        pos =data.find(toSearch, pos + toSearch.size());
      }
  }
  	
  string format_string(string input, unordered_map<string, string> replace_map) {
    string output = input;
    for (auto replace : replace_map) {
      findAndReplaceAll(output, replace.first, replace.second);
    }
    return output;
  }
  
}

namespace CoreIR {
  namespace Passes {

    string SMVgetCurr(string context, string var) {return "\"" + context + var + "\""; }
    string SMVgetNext(string context, string var) {return "next(" + SMVgetCurr(context, var) + ")"; }

    SmvBVVar SmvBVVarGetNext(SmvBVVar var) {
      var.setName(SMVgetNext("", var.getName()));
      return var;
    }

    SmvBVVar SmvBVVarGetCurr(SmvBVVar var) {
      var.setName(SMVgetCurr("", var.getName()));
      return var;
    }

    string SmvBVVarDec(SmvBVVar w) {
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

    string SMVBop(string context, string opname, string op, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      // INVAR: (in1 <op> in2) = out
      string in1 = in1_p.getPortName();
      string in2 = in2_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMV" + opname + " (in1, in2, out) = (" + in1 + ", " + in2 + ", " + out + ")";
      string curr = binary_op_eq(op, SMVgetCurr(context, in1), SMVgetCurr(context, in2), SMVgetCurr(context, out));
      return comment + NL + get_invar(curr);
    }

    string SMVAnd(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      return SMVBop(context, "And", "&", in1_p, in2_p, out_p);
    }

    string SMVOr(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      return SMVBop(context, "Or", "|", in1_p, in2_p, out_p);
    }

    string SMVXor(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      return SMVBop(context, "Xor", "xor", in1_p, in2_p, out_p);
    }
    
    string SMVAdd(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      return SMVBop(context, "Add", "+", in1_p, in2_p, out_p);
    }

    string SMVSub(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      return SMVBop(context, "Sub", "-", in1_p, in2_p, out_p);
    }
    
    string SMVConcat(string context, SmvBVVar in1_p, SmvBVVar in2_p, SmvBVVar out_p) {
      return SMVBop(context, "Concat", "::", in1_p, in2_p, out_p);
    }

    string SMVSlice(string context, SmvBVVar in_p, SmvBVVar out_p, int low_p, int high_p) {
      // INVAR: (in[high:low] = out)
      string in = in_p.getPortName();
      string out = out_p.getPortName();
      string low = to_string(low_p);
      string high = to_string(high_p);
      string comment = "-- SMVSlice (in, out, low, high) = (" + in + ", " + out + ", " + low + ", " + high + ")";
      string op = "[" + high + ":" + low + "]";
      string curr = SMVgetCurr(context, in) + op + "=" + SMVgetCurr(context, out);
      return comment + NL + get_invar(curr);
    }
    
    string SMVNot(string context, SmvBVVar in_p, SmvBVVar out_p) {
      // INVAR: (!in = out)
      string in = in_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMVNot (in, out) = (" + in + ", " + out + ")";
      string op = "!";
      string curr = unary_op_eq(op, SMVgetCurr(context, in), SMVgetCurr(context, out));
      return comment + NL + get_invar(curr);
    }

    string SMVConst(string context, SmvBVVar out_p, int val) {
      // INVAR: (out = val)
      string out = out_p.getPortName();
      string vals = getSMVbits(stoi(out_p.dimstr()), val);
      string comment = "-- SMVConst (out, val) = (" + out + ", " + vals + ")";
      string curr = binary_op("=", SMVgetCurr(context, out), vals);
      return comment + NL + get_invar(curr);
    }

    string SMVReg(string context, SmvBVVar in_p, SmvBVVar clk_p, SmvBVVar out_p) {
      // INIT: out = 0
      // TRANS: ((!clk & clk') -> (out' = in)) & (!(!clk & clk') -> (out' = out))
      string in = in_p.getPortName();
      string clk = clk_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMVReg (in, clk, out) = (" + in + ", " + clk + ", " + out + ")";
      
      unordered_map<string, string> replace_map;
      replace_map.emplace("{clk}", SMVgetCurr(context, clk));
      replace_map.emplace("{out}", SMVgetCurr(context, out));
      replace_map.emplace("{in}", SMVgetCurr(context, in));
      replace_map.emplace("{zero}", getSMVbits(stoi(out_p.dimstr()), 0));
      
      string trans = "(((!{clk} & next({clk})) = 0ud1_1) -> (next({out}) = {in})) & ((!(!{clk} & next({clk})) = 0ud1_1) -> (next({out}) = {out}))";
      string init = "{out} = {zero}";
      
      trans = format_string(trans, replace_map);      
      init = format_string(init, replace_map);      
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
      
      unordered_map<string, string> replace_map;
      replace_map.emplace("{en}", SMVgetCurr(context, en));
      replace_map.emplace("{clk}", SMVgetCurr(context, clk));
      replace_map.emplace("{out}", SMVgetCurr(context, out));
      replace_map.emplace("{in}", SMVgetCurr(context, in));
      replace_map.emplace("{zero}", getSMVbits(stoi(out_p.dimstr()), 0));
      
      string trans = "((({en} & !{clk} & next({clk})) = 0ud1_1) -> (next({out}) = {in})) & ((!({en} & !{clk} & next({clk})) = 0ud1_1) -> (next({out}) = {out}))";
      string init = "{out} = {zero}";
      
      trans = format_string(trans, replace_map);      
      init = format_string(init, replace_map);      
      return comment + NL + get_init(init) + NL + get_trans(trans);
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

    string SMVMux(string context, SmvBVVar in0_p, SmvBVVar in1_p, SmvBVVar sel_p, SmvBVVar out_p) {
      string in0 = in0_p.getPortName();
      string in1 = in1_p.getPortName();
      string sel = sel_p.getPortName();
      string out = out_p.getPortName();
      string comment = "-- SMVMux (in0, in1, sel, out) = (" + in0 + ", " + in1 + ", " + sel + ", " + out + ")";

      string one = "0ud1_1";
      string zero = "0ud1_0";
      
      string then_bc = binary_op("=", SMVgetCurr(context, sel), one);
      string else_bc = binary_op("=", SMVgetCurr(context, sel), zero);
      string curr_1 = binary_op("->", then_bc, binary_op("=", SMVgetCurr(context, in0), SMVgetCurr(context, out)));
      string curr_2 = binary_op("->", else_bc, binary_op("=", SMVgetCurr(context, in1), SMVgetCurr(context, out)));
      string invar = binary_op("&", curr_1, curr_2);

      return comment + NL + get_invar(invar);
    }

    
    string SMVProperty(string name, PropType type, string value) {
      string ptype = type == invarspec ? "INVARSPEC" : "LTLSPEC";
      return ptype + " NAME\n" + name + " := " + value + ";";
    }
  }
}
