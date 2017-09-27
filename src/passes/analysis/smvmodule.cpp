#include "coreir.h"
#include "coreir/passes/analysis/smvmodule.hpp"
#include "coreir/passes/analysis/smvoperators.hpp"

#include <iostream>
using namespace CoreIR;
using namespace Passes;
using namespace std;

typedef void (*voidFunctionType)(void);

string SMVModule::toString() {
  ostringstream o;
  string tab = "  ";

  //Param declaraions
  for (auto p : params) {
    o << tab << "parameter " << p;
    if (paramDefaults.count(p)) {
      o << " = " << paramDefaults[p];
    }
    o << ";" << endl;
  }
  o << endl;
  
  for (auto s : stmts) o << s << endl;
  return o.str();
}

string SMVModule::toVarDecString() {
  ostringstream o;
  for (auto vd : vardecs) o << vd << endl;
  return o.str();
}

string SMVModule::toNextVarDecString() {
  ostringstream o;
  for (auto vd : nextvardecs) o << vd << endl;
  return o.str();
}

string SMVModule::toInitVarDecString() {
  ostringstream o;
  for (auto vd : initvardecs) o << vd << endl;
  return o.str();
}

string SMVModule::toInstanceString(Instance* inst, string path) {
  string instname = inst->getInstname();
  Instantiable* iref = inst->getInstantiableRef();
  if (this->gen) {
    ASSERT(inst->isGen(),"DEBUG ME:");
  }
  ostringstream o;
  string tab = "  ";
  string mname;
  Args args;
  if (gen) {
    args = inst->getGenArgs();
    addPortsFromGen(inst);
    mname = gen->getNamespace()->getName() + SEP + gen->getName(args);
  }
  else {
    mname = modname;
  }

  for (auto amap : inst->getConfigArgs()) {
    ASSERT(args.count(amap.first)==0,"NYI Alisaaed config/genargs");
    args[amap.first] = amap.second;
  }
  vector<string> params;
  const json& jmeta = iref->getMetaData();
  // json& jprop = iref->getProperty();

  // unordered_map<string, PropDef> properties;
  // if (jprop.size()) {
  //   //    cout << "PROPERTY: " << jprop << endl;
  //   for (int i=0; i<jprop.size(); i++) {
  //     string propname = jprop[0][0];
  //     PropType ptype = jprop[0][1] == "invar" ? invarspec : ltlspec;
  //     string propval = jprop[0][2];
  //     PropDef prop = make_pair(ptype, propval);
  //     properties.emplace(propname, prop);
  //   }
  // }

  // for (auto property : properties) {
  //   cout << property.first << " " << property.second.first << " " << property.second.second << endl;
  // }
  
  if (jmeta.count("verilog") && jmeta["verilog"].count("parameters")) {
    params = jmeta["verilog"]["parameters"].get<vector<string>>();
  }
  else {
    for (auto amap : args) {
      params.push_back(amap.first);
    }
  }
  vector<string> paramstrs;
  for (auto param : params) {
    ASSERT(args.count(param),"Missing parameter " + param + " from " + Args2Str(args));
    string astr = "." + param + "(" + args[param]->toString() + ")";
    paramstrs.push_back(astr);
  }
  //Assume names are <instname>_port
  unordered_map<string, SmvBVVar> portstrs;
  for (auto port : ports) {
    portstrs.emplace(port.getPortName(), port);
  }

  string context = path+SEP;
  string pre = "coreir"+SEP;

  enum operation {neg_op = 1,
                  const_op,
                  add_op,
                  and_op,
                  or_op,
                  reg_op,
                  regPE_op,
                  concat_op,
                  slice_op,
                  term_op};

  unordered_map<string, operation> opmap;

  opmap.emplace(pre+"neg", neg_op);
  opmap.emplace(pre+"const", const_op);
  opmap.emplace(pre+"add", add_op);
  opmap.emplace(pre+"and", and_op);
  opmap.emplace(pre+"or", or_op);
  opmap.emplace(pre+"reg", reg_op);
  opmap.emplace(pre+"reg_PE", regPE_op);
  opmap.emplace(pre+"concat", concat_op);
  opmap.emplace(pre+"slice", slice_op);
  opmap.emplace(pre+"term", term_op);

#define var_assign(var, name) if (portstrs.find(name) != portstrs.end()) var = portstrs.find(name)->second
  
  SmvBVVar out; var_assign(out, "out");
  SmvBVVar in; var_assign(in, "in");
  SmvBVVar in0; var_assign(in0, "in0");
  SmvBVVar in1; var_assign(in1, "in1");
  SmvBVVar clk; var_assign(clk, "clk");
  SmvBVVar en; var_assign(en, "en");
  
  switch (opmap[mname]) {
  case term_op:
    break;
  case neg_op:
    o << SMVNot(context, in, out);
    break;
  case add_op:
    o << SMVAdd(context, in0, in1, out);
    break;
  case and_op:
    o << SMVAnd(context, in0, in1, out);
    break;
  case or_op:
    o << SMVOr(context, in0, in1, out);
    break;
  case concat_op:
    o << SMVConcat(context, in0, in1, out);
    break;
  case regPE_op:
    o << SMVRegPE(context, in, clk, out, en);
    break;
  case const_op:
    int width; width = stoi(args["width"]->toString());
    int value; value = stoi(args["value"]->toString());
    o << SMVConst(context, out, getSMVbits(width, value));
    break;
  case slice_op:
    int lo; lo = stoi(args["lo"]->toString());
    int hi; hi = stoi(args["hi"]->toString());
    o << SMVSlice(context, in, out, lo, hi-1);
    break;
  default:
    o << "!!! UNMATCHED: " << mname << " !!!";
  }
  
  o << endl;
  return o.str();
}

