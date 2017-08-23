#include "coreir.h"
#include "coreir-passes/analysis/smtmodule.hpp"
#include "coreir-passes/analysis/smtoperators.hpp"

using namespace CoreIR;
using namespace Passes;

typedef void (*voidFunctionType)(void);

string SMTModule::toString() {
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

string SMTModule::toVarDecString() {
  ostringstream o;
  for (auto vd : vardecs) o << vd << endl;
  return o.str();
}

string SMTModule::toInstanceString(Instance* inst) {
  string instname = inst->getInstname();
  Instantiable* iref = inst->getInstantiableRef();
  if (this->gen) {
    ASSERT(inst->isGen(),"DEBUG ME:");
  }
  ostringstream o;
  string tab = "  ";
  string mname;
  unordered_map<string,SmtBVVar> iports;
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
  vector<std::pair <string, SmtBVVar>> portstrs;
  for (auto port : iports) {
    std::pair<string, SmtBVVar> pstr = std::make_pair(instname, port.second);
    portstrs.push_back(pstr);
  }

  bool matched = false;
  if (mname == "coreir_neg") {o << SMTNot(portstrs.at(0), portstrs.at(1)); matched = true;}
  if (mname == "coreir_const") {
    o << SMTConst(portstrs.at(0), getSMTbits(stoi(args["width"]->toString()), stoi(args["value"]->toString())));
    matched = true;
  }
  if (mname == "coreir_add") {o << SMTAdd(portstrs.at(0), portstrs.at(1), portstrs.at(2)); matched = true;}
  if (mname == "coreir_reg_PE") {o << SMTRegPE(portstrs.at(0), portstrs.at(1), portstrs.at(2), portstrs.at(3)); matched = true;}
  if (mname == "counter") {o << SMTCounter(portstrs.at(0), portstrs.at(1), portstrs.at(2)); matched = true;}
  if (mname == "coreir_concat") {o << SMTConcat(portstrs.at(0), portstrs.at(1), portstrs.at(2)); matched = true;}
  
  if (!matched) {
    o << "Unmatched: " << mname << endl;
    //    o << mname << "(\n" << tab << tab << join(portstrs.begin(),portstrs.end(),",\n"+tab+tab) << "\n  );" << endl;
  }
              
  return o.str();
}

