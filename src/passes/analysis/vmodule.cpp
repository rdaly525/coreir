#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"

using namespace CoreIR;
using namespace CoreIR::Passes;
using namespace std;

string VModule::toString() {
  vector<string> pdecs;
  if (interface.size()>0) {
    pdecs = interface;
  }
  else {
    for (auto pmap : ports) {
      auto port = pmap.second;
      pdecs.push_back(port.dirstr() + " " + port.dimstr() + " " + port.getName());
    }
  }
  
  vector<string> paramstrs;
  for (auto p : params) {
    string s = "parameter " + p + "=" + (paramDefaults.count(p)>0 ? paramDefaults[p] : "1"); 
    paramstrs.push_back(s);
  }
  string pstring = paramstrs.size()>0 ? " #(" + join(paramstrs.begin(),paramstrs.end(),string(", "))+") " : " ";

  ostringstream o;
  string tab = "  ";
  //Module declaration
  o << endl << "module " << modname << pstring << "(\n" << tab << join(pdecs.begin(),pdecs.end(),string(",\n  ")) << "\n);" << endl;

  for (auto s : stmts) o << s << endl;
  o << endl << "endmodule //" << modname;
  return o.str();
}

string VModule::toInstanceString(Instance* inst) {
  string instname = inst->getInstname();
  Module* mref = inst->getModuleRef();
  SParams params0 = params;
  if (this->gen) {
    assert(mref->isGenerated());
    auto paramsAndDefaults = gen->getModParams(mref->getGenArgs());
    if (!this->hasDef()) {
      this->addParams(params0,paramsAndDefaults.first);
    }
  }

  ostringstream o;
  string tab = "  ";
  string mname;
  map<string,VWire> iports;
  Values args;
  if (gen) {
    args = mref->getGenArgs();
    Type2Ports(gen->getTypeGen()->getType(args),iports);
    mname = modname; 
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
  
  vector<string> paramstrs;
  for (auto param : params0) {
    ASSERT(args.count(param),"Missing parameter " + param + " from " + ::CoreIR::toString(args));
    string astr = "." + param + "(" + toConstString(args[param]) + ")";
    paramstrs.push_back(astr);
  }
  if (paramstrs.size()) {
    o << "#(" << join(paramstrs.begin(),paramstrs.end(),string(",")) << ") ";
  }
  //Assume names are <instname>_port
  vector<string> portstrs;
  for (auto port : iports) {
    string pstr = "."+port.first+"(" + instname+"__"+ port.first+")";
    portstrs.push_back(pstr);
  }
  o << instname << "(\n" << tab << tab << join(portstrs.begin(),portstrs.end(),",\n"+tab+tab) << "\n  );" << endl;
  return o.str();
}

