#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

string VModule::toString() {
  vector<string> pdecs;
  for (auto pmap : ports) {
    auto port = pmap.second;
    pdecs.push_back(port.dirstr() + " " + port.dimstr() + " " + port.getName());
  }
  ostringstream o;
  string tab = "  ";
  //Module declaration
  o << endl << "module " << modname << "(\n" << tab << join(pdecs.begin(),pdecs.end(),string(",\n  ")) << "\n);" << endl;

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
  o << endl << "endmodule //" << modname;
  return o.str();
}

string VModule::toInstanceString(Instance* inst) {
  string instname = inst->getInstname();
  Instantiable* iref = inst->getInstantiableRef();
  if (this->gen) {
    ASSERT(inst->isGen(),"DEBUG ME:");
    auto paramsAndDefaults = gen->getModParams(inst->getGenArgs());
    this->addParams(paramsAndDefaults.first);
    this->addDefaults(paramsAndDefaults.second);
  }
  ostringstream o;
  string tab = "  ";
  string mname;
  unordered_map<string,VWire> iports;
  Values args;
  if (gen) {
    args = inst->getGenArgs();
    Type2Ports(gen->getTypeGen()->getType(inst->getGenArgs()),iports);
    mname = gen->getNamespace()->getName() + "_" + modname; //TODO bug
  }
  else {
    mname = modname;
    iports = ports;
  }

  for (auto amap : inst->getModArgs()) {
    ASSERT(args.count(amap.first)==0,"NYI Alisaaed modargs/genargs");
    args[amap.first] = amap.second;
  }
  o << tab << mname << " ";
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
    ASSERT(args.count(param),"Missing parameter " + param + " from " + Values2Str(args));
    string astr = "." + param + "(" + args[param]->toString() + ")";
    paramstrs.push_back(astr);
  }
  if (paramstrs.size()) {
    o << "#(" << join(paramstrs.begin(),paramstrs.end(),string(",")) << ") ";
  }
  //Assume names are <instname>_port
  vector<string> portstrs;
  for (auto port : iports) {
    string pstr = "."+port.first+"(" + instname+"_"+ port.first+")";
    portstrs.push_back(pstr);
  }
  o << instname << "(\n" << tab << tab << join(portstrs.begin(),portstrs.end(),",\n"+tab+tab) << "\n  );" << endl;
  return o.str();
}

