#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"

namespace CoreIR {
namespace Passes {
namespace VerilogNamespace {



CoreIRVModule::CoreIRVModule(VModules* vmods, Module* m) : VModule(vmods) {
  Type2Ports(m->getType(),this->ports);
  assert(m->hasDef());
  this->modname = m->getLongName();
  if (m->isGenerated()) {
    this->modComment = "// Generated from " + m->getRefName() + ::CoreIR::toString(m->getGenArgs());
  }
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
    this->addStmt("");
    if (file != "_") {
      this->addComment("Compiled from " + file);
    }
    for (auto vobj : fpair.second) {
      this->addStmt("");
      vobj->materialize(this);
    }
    this->addStmt("");
  }
}

void CoreIRVModule::addConnection(ModuleDef* def, Connection conn) {
  VObject* vass = new VAssign(def,conn);
  conn2VObj[conn] = vass;
  sortedVObj[vass->file].insert(vass);
}
//Need to choose if I am going to inline
void CoreIRVModule::addInstance(Instance* inst) {
  Module* mref = inst->getModuleRef();
  VModule* vmref = vmods->mod2VMod[mref];
  VObject* vinst;
  if (auto vermod = dynamic_cast<VerilogVModule*>(vmref)) {
    if (vmods->_inline && vermod->inlineable) {
      vinst = new VInlineInstance(this->vmods,inst,vermod);
    } 
    else {
      vinst = new VInstance(this->vmods,inst);
    }
  }
  else {
    vinst = new VInstance(this->vmods,inst);
  }
  inst2VObj[inst] = vinst;
  sortedVObj[vinst->file].insert(vinst);
}

bool VObjComp::operator() (const VObject* l, const VObject* r) const {
  if (l->line != r->line) {
    return l->line < r->line;
  }
  if (l->priority != r->priority) {
    return l->priority < r->priority;
  }
  return l->name < r->name;
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
  //cout << isGen << hasDef << genHasVerilog << modHasVerilog << isExtern << mightHaveVmodule << endl;
  
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

string VModule::toString() const {
  // In the case that we want to blackbox the entirety of the module source, we
  // just return the verilog_string field.
  if (verilog_string != "") {
    return verilog_string;
  }

  assert(this->modname != "");
  vector<string> pdecs;
  if (interface.size()>0) {
    pdecs = interface;
  }
  else {
    for (auto pmap : ports) {
      auto port = pmap.second;
      string pdec = port.dirstr() + " " + port.dimstr() + " " + port.getName();
      if (this->vmods->_verilator_debug) {
          pdec += "/*verilator public*/";
      }
      pdecs.push_back(pdec);
    }
  }
  
  vector<string> paramstrs;
  for (auto p : params) {

    // TODO: Find a better way to deal with type parameters in wrap
    if (p != "type") {
      string s = "parameter " + p + "=" + (paramDefaults.count(p)>0 ? paramDefaults.at(p) : "1");
      paramstrs.push_back(s);
    }
  }
  string pstring = paramstrs.size()>0 ? " #(" + join(paramstrs.begin(),paramstrs.end(),string(", "))+") " : " ";

  ostringstream o;
  string tab = "  ";
  //Module declaration
  
  if (this->modComment!="") {
    o << this->modComment << endl;
  }
  o << "module " << modname << pstring << "(\n" << tab << join(pdecs.begin(),pdecs.end(),string(",\n  ")) << "\n);" << endl;

  for (auto s : stmts) o << s << endl;
  o << endl << "endmodule  // " << modname << endl;
  return o.str();
}

string VModule::toInstanceString(Instance* inst) {
  assert(this->modname != "");
  string instname = inst->getInstname();
  Module* mref = inst->getModuleRef();
  SParams params_bk = this->params;

  ostringstream o;
  string tab = "  ";
  string mname;
  map<string,VWire> iports;
  Values args;
  bool isVerilogGen = mref->isGenerated() && mref->getGenerator()->getMetaData().count("verilog") > 0;
  if (isVerilogGen) {
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
  o << instname << "(\n" << tab << tab << join(portstrs.begin(),portstrs.end(),",\n"+tab+tab) << "\n  );";

  //TODO a bit of a hack. return params to original
  this->params = params_bk;

  return o.str();
}


}
}
}
