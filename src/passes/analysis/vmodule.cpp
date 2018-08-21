#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"

namespace CoreIR {
namespace Passes {
namespace VerilogNamespace {



CoreIRVModule::CoreIRVModule(VModules* vmods, Module* m) : VModule(vmods) {
  Type2Ports(m->getType(),this->ports);
  assert(m->hasDef());
  this->modname = m->getNamespace()->getName() + "_" + m->getName();
  this->addParams(m->getModParams());
  this->addDefaults(m->getDefaultModArgs());
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
    if (file != "_") {
      this->addComment("From " + file);
    }
    for (auto vobj : fpair.second) {
      vobj->materialize(this);
    }
  }
}

void CoreIRVModule::addConnection(ModuleDef* def, Connection conn) {
  VObject* vass = new VAssign(def,conn);
  conn2VObj[conn] = vass;
  sortedVObj[vass->file].insert(vass);
}
void CoreIRVModule::addInstance(Instance* inst) {
  VObject* vinst = new VInstance(this->vmods,inst);
  inst2VObj[inst] = vinst;
  sortedVObj[vinst->file].insert(vinst);
}

bool VObjComp::operator() (const VObject* l, const VObject* r) const {
  if (l->line == r->line) {
    return l->name < r->name;
  }
  return l->line < r->line;
}

//Orthog Cases:
// Generated Module
// Has coreir def
// Generator has verilog info
// Module has verilog info
void VModules::addModule(Module* m) {
  cout << "vmoding: " <<m->toString() << endl;
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
  cout << isGen << hasDef << genHasVerilog << modHasVerilog << isExtern << mightHaveVmodule << endl;
  
  //Already Created modules
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
    assert(gen2VMod.count(g)==0);
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
  vmods.push_back(vmod);
}

string VModule::toString() {
  assert(this->modname != "");
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
  assert(this->modname != "");
  cout << "Instance = " << inst->toString() << endl;
  for (auto p : this->params) {
    cout << "  " << p << endl;
  }
  cout << endl;
  string instname = inst->getInstname();
  Module* mref = inst->getModuleRef();
  SParams params_bk = this->params;
  //if (mref->isGenerated()) {
  //  auto modparams = mref->getModParams();
  //  this->addParams(modparams);
  //}

  ostringstream o;
  string tab = "  ";
  string mname;
  map<string,VWire> iports;
  Values args;
  if (mref->isGenerated()) {
    args = mref->getGenArgs();
    Type2Ports(mref->getGenerator()->getTypeGen()->getType(args),iports);
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
  for (auto param : this->params) {
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

  //TODO a bit of a hack. return params to original
  this->params = params_bk;

  return o.str();
}


}
}
}
