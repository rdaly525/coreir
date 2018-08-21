#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"

namespace CoreIR {
namespace Passes {
namespace Verilog {



CoreIRVModule::CoreIRVModule(VModules* vmods, Module* m) : VModule(vmods) {
  Type2Ports(m->getType(),this->ports);
  assert(m->hasDef());
  ModuleDef* def = m->getDef();
  for (auto imap : def->getInstances()) {
    this->addInstance(imap.second);
  }
  for (auto con : def->getConnections()) {
    this->addConnection(def,con);
  }
  //Materialize all the statemts
  for (auto fpair : sortedVObj) {
    string file = fpair.first;
    this->addComment("From " + file);
    for (auto vobj : fpair.second) {
      vobj->materialize(this);
    }
  }
}

void CoreIRVModule::addConnection(ModuleDef* def, Connection conn) {
  VObject* vass = new VAssign(def,conn);
  conn2VObj[conn] = vass;
  sortedVObj[vass.file].insert(vass);
}
void CoreIRVModule::addInstance(Instance* inst) {
  VObject* vinst = new VInstance(this->vmods,inst);
  conn2VObj[conn] = vinst;
  sortedVObj[vinst.file].insert(vinst);
}

bool VObjComp::operator() (const VObject*& l, const VObject*& r) const {
  return l->line < r->line;
}

//Orthog Cases:
// Generated Module
// Has coreir def
// Generator has verilog info
// Module has verilog info
void VModules::addModule(Module* m) {
  Generator* g = nullptr;
  bool isGen = m->isGenerated();
  if (isGen) {
    g = m->getGenerator();
  }
  bool hasDef = m->hasDef();
  bool genHasVerilog = false;
  if (isGen) {
    genHasVerilog = g->getMetaData().count("verilog") > 0;
  }
  bool modHasVerilog = m->getMetaData().count("verilog") > 0;
  
  //Linking concerns:
  //coreir Def and Verilog Def
  //TODO should probably let the verilog def override the coreir def
  if (hasDef) {
    ASSERT(!genHasVerilog && !modHasVerilog,"NYI, Verilog def with coreir def");
  }
  //Two Verilog defs, should be an error
  ASSERT(!(modHasVerilog && genHasVerilog),"Linking issue!");

  bool isExtern = !hasDef && !genHasVerilog && !modHasVerilog;
  
  //Case where VModule might already exist
  bool mightHaveVmodule = isGen && genHasVerilog;
  if (mightHaveVmodule && gen2VMod.count(g) > 0) {
    mod2VMod[m] = gen2VMod[g];
    return;
  }
  
  //Creating a new VModule
  VModule* vmod;
  if (isExtern) {
    vmod = new ExternVModule(this,m);
    externalVMods.push_back(vmod);
  }
  else if (genHasVerilog) {
    assert(gen2Vmod.count(g)==0);
    vmod = new ParamVerilogVModule(this,g);
    gen2VMod[g] = vmod;
  }
  else if (modHasVerilog) {
    vmod = new VerilogVModule(this,m);
  }
  else {
    //m is either gen or not
    vmod = new CoreIRVModule(this,m);
  }
  mod2VMod[m] = vmod;
}

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

    // TODO: Find a better way to deal with type parameters in wrap
    if (p != "type") {
      string s = "parameter " + p + "=" + (paramDefaults.count(p)>0 ? paramDefaults[p] : "1"); 
      paramstrs.push_back(s);
    }
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
  //cout << "Instance = " << inst->toString() << endl;
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

    // TODO: Remove this when we have a better solution for verilog output
    if (param != "type") {
      string astr = "." + param + "(" + toConstString(args[param]) + ")";
      paramstrs.push_back(astr);
    }
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


}
}
}
