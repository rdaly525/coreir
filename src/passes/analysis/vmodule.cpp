#include "coreir.h"
#include "coreir-passes/analysis/vmodule.hpp"

using namespace CoreIR;

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
  Args args = inst->getConfigArgs();
  if (inst->isGen()) {
    for (auto amap : inst->getGenArgs()) {
      ASSERT(args.count(amap.first)==0,"NYI: aliasing config/args");
      args[amap.first] = amap.second;
    }
  }
  ostringstream o;
  string tab = "  ";
  string mname;
  unordered_map<string,VWire> iports;
  if (gen) {
    mname = gen->getNamespace()->getName() + "_" + gen->getName(args);
    Type2Ports(gen->getTypeGen()->getType(args),iports);
  }
  else {
    mname = modname;
    iports = ports;
  }

  o << tab << mname << " ";
  vector<string> paramstrs;
  for (auto amap : args) {
    string astr = "." + amap.first + "(" + amap.second->toString() + ")";
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

