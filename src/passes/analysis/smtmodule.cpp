#include "coreir.h"
#include "coreir-passes/analysis/smtmodule.hpp"
#include "coreir-passes/analysis/smtoperators.hpp"

#include <iostream>
using namespace CoreIR;
using namespace Passes;

typedef void (*voidFunctionType)(void);

string SMTModule::toString() {
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

string SMTModule::toVarDecString() {
  ostringstream o;
  for (auto vd : vardecs) o << vd << endl;
  return o.str();
}

string SMTModule::toNextVarDecString() {
  ostringstream o;
  for (auto vd : nextvardecs) o << vd << endl;
  return o.str();
}

string SMTModule::toInitVarDecString() {
  ostringstream o;
  for (auto vd : initvardecs) o << vd << endl;
  return o.str();
}

string SMTModule::toInstanceString(Instance* inst, string path) {
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
  unordered_map<string, SmtBVVar> portstrs;
  for (auto port : ports) {
    portstrs.emplace(port.getPortName(), port);
  }

  string context = path+ SEP;
  
  if (mname == "coreir"+SEP+"neg")
    o << SMTNot(context, portstrs.find("in")->second, portstrs.find("out")->second);
  else if (mname == "coreir"+SEP+"const")
    o << SMTConst(context, portstrs.find("out")->second, getSMTbits(stoi(args["width"]->toString()), stoi(args["value"]->toString())));
  else if (mname == "coreir"+SEP+"add")
    o << SMTAdd(context, portstrs.find("in0")->second, portstrs.find("in1")->second, portstrs.find("out")->second);
  else if (mname == "coreir"+SEP+"reg_PE")
    o << SMTRegPE(context, portstrs.find("in")->second, portstrs.find("clk")->second, portstrs.find("out")->second, portstrs.find("en")->second);
  // else if (mname == "counter")
  //   o << SMTCounter(portstrs.find("clk")->second, portstrs.find("en")->second, portstrs.find("out")->second);
  else if (mname == "coreir"+SEP+"concat")
    o << SMTConcat(context, portstrs.find("in0")->second, portstrs.find("in1")->second, portstrs.find("out")->second);
  else if (mname == "coreir"+SEP+"slice") {
    int lo = stoi(args["lo"]->toString());
    int hi = stoi(args["hi"]->toString())-1;
    o << SMTSlice(context, portstrs.find("in")->second, portstrs.find("out")->second,
		  std::to_string(lo), std::to_string(hi)) << endl;
  }
  else if (mname == "coreir"+SEP+"term"); // do nothing in terminate case
  else {
    o << "!!! UNMATCHED: " << mname << " !!!" << endl;
    //    o << mname << "(\n" << tab << tab << join(portstrs.begin(),portstrs.end(),",\n"+tab+tab) << "\n  );" << endl;
  }
              
  return o.str();
}

