#include "coreir.h"
#include "coreir-passes/analysis/vmtmodule.hpp"
#include "coreir-passes/analysis/vmtoperators.hpp"

#include <iostream>
using namespace CoreIR;
using namespace Passes;

typedef void (*voidFunctionType)(void);

string VMTModule::toString() {
  vector<string> pdecs;
  for (auto pmap : ports) {
    auto port = pmap.second;
    pdecs.push_back(port.getName() + " () " + "(_ BitVec " + port.dimstr() + ")");
  }
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

string VMTModule::toVarDecString() {
  ostringstream o;
  for (auto vd : vardecs) o << vd << endl;
  return o.str();
}

string VMTModule::toNextVarDecString() {
  ostringstream o;
  for (auto vd : nextvardecs) o << vd << endl;
  return o.str();
}

string VMTModule::toInitVarDecString() {
  ostringstream o;
  for (auto vd : initvardecs) o << vd << endl;
  return o.str();
}

string VMTModule::toInstanceString(Instance* inst) {
  string instname = inst->getInstname();
  Instantiable* iref = inst->getInstantiableRef();
  if (this->gen) {
    ASSERT(inst->isGen(),"DEBUG ME:");
  }
  ostringstream o;
  string tab = "  ";
  string mname;
  unordered_map<string,VmtBVVar> iports;
  Args args;
  if (gen) {
    args = inst->getGenArgs();
    Type2Ports(gen->getTypeGen()->getType(inst->getGenArgs()),iports);
    mname = gen->getNamespace()->getName() + "_" + gen->getName(args);
  }
  else {
    mname = modname;
    iports = ports;
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
  unordered_map<string, std::pair <string, VmtBVVar>> portstrs;
  for (auto port : iports) {
    pair<string, VmtBVVar> pstr = std::make_pair(instname, port.second);
    portstrs.emplace(port.first, pstr);
  }

  if (mname == "coreir_neg")
    o << VMTNot(portstrs.find("in")->second, portstrs.find("out")->second);
  else if (mname == "coreir_const")
    o << VMTConst(portstrs.find("out")->second, getVMTbits(stoi(args["width"]->toString()), stoi(args["value"]->toString())));
  else if (mname == "coreir_add")
    o << VMTAdd(portstrs.find("in0")->second, portstrs.find("in1")->second, portstrs.find("out")->second);
  else if (mname == "coreir_reg_PE")
    o << VMTRegPE(portstrs.find("in")->second, portstrs.find("clk")->second, portstrs.find("out")->second, portstrs.find("en")->second);
  else if (mname == "counter")
    o << VMTCounter(portstrs.find("clk")->second, portstrs.find("en")->second, portstrs.find("out")->second);
  else if (mname == "coreir_concat")
    o << VMTConcat(portstrs.find("in0")->second, portstrs.find("in1")->second, portstrs.find("out")->second);
  else if (mname == "coreir_slice") {
    int lo = stoi(args["lo"]->toString());
    int hi = stoi(args["hi"]->toString())-1;
    o << VMTSlice(portstrs.find("in")->second, portstrs.find("out")->second,
		  std::to_string(lo), std::to_string(hi)) << endl;
  }
  else if (mname == "coreir_term"); // do nothing in terminate case
  else {
    o << "!!! UNMATCHED: " << mname << " !!!" << endl;
    //    o << mname << "(\n" << tab << tab << join(portstrs.begin(),portstrs.end(),",\n"+tab+tab) << "\n  );" << endl;
  }
              
  return o.str();
}

