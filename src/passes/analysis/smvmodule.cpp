#include "coreir.h"
#include "coreir-passes/analysis/smvmodule.hpp"
#include "coreir-passes/analysis/smvoperators.hpp"

#include <iostream>
using namespace CoreIR;
using namespace Passes;

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
    mname = gen->getNamespace()->getName() + SEP_SMV + gen->getName(args);
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
  unordered_map<string, SmvBVVar> portstrs;
  for (auto port : ports) {
    portstrs.emplace(port.getPortName(), port);
  }

  string context = path+ SEP_SMV;
  
  if (mname == "coreir"+SEP_SMV+"neg")
    o << SMVNot(context, portstrs.find("in")->second, portstrs.find("out")->second);
  else if (mname == "coreir"+SEP_SMV+"const")
    o << SMVConst(context, portstrs.find("out")->second, getSMVbits(stoi(args["width"]->toString()), stoi(args["value"]->toString())));
  else if (mname == "coreir"+SEP_SMV+"add")
    o << SMVAdd(context, portstrs.find("in0")->second, portstrs.find("in1")->second, portstrs.find("out")->second);
  else if (mname == "coreir"+SEP_SMV+"reg_PE")
    o << SMVRegPE(context, portstrs.find("in")->second, portstrs.find("clk")->second, portstrs.find("out")->second, portstrs.find("en")->second);
  // else if (mname == "counter")
  //   o << SMVCounter(portstrs.find("clk")->second, portstrs.find("en")->second, portstrs.find("out")->second);
  else if (mname == "coreir"+SEP_SMV+"concat")
    o << SMVConcat(context, portstrs.find("in0")->second, portstrs.find("in1")->second, portstrs.find("out")->second);
  else if (mname == "coreir"+SEP_SMV+"slice") {
    int lo = stoi(args["lo"]->toString());
    int hi = stoi(args["hi"]->toString())-1;
    o << SMVSlice(context, portstrs.find("in")->second, portstrs.find("out")->second,
		  std::to_string(lo), std::to_string(hi)) << endl;
  }
  else if (mname == "coreir"+SEP_SMV+"term"); // do nothing in terminate case
  else {
    o << "!!! UNMATCHED: " << mname << " !!!" << endl;
    //    o << mname << "(\n" << tab << tab << join(portstrs.begin(),portstrs.end(),",\n"+tab+tab) << "\n  );" << endl;
  }
              
  return o.str();
}

