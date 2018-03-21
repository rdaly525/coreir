#include "coreir.h"
#include "coreir/passes/analysis/vmodule.h"
#include "coreir/passes/analysis/verilog.h"

using namespace std;
using namespace CoreIR;
using namespace CoreIR::Passes;

namespace {

string VWireDec(VWire w) { return "  wire " + w.dimstr() + " " + w.getName() + ";"; }


string VAssign(Connection con) {
  Wireable* left = con.first->getType()->getDir()==Type::DK_In ? con.first : con.second;
  Wireable* right = left==con.first ? con.second : con.first;
  VWire vleft(left);
  VWire vright(right);
  return "  assign " + vleft.getName() + vleft.dimstr() + " = " + vright.getName() + vright.dimstr() + ";";
}

}

std::string Passes::Verilog::ID = "verilog";
bool Passes::Verilog::runOnInstanceGraphNode(InstanceGraphNode& node) {
  
  //Create a new Vmodule for this node
  Module* m = node.getModule();
  cout << "Creating verilog for " << m->getRefName() << endl;
  if (m->isGenerated() && !m->hasDef()) { //TODO linking concern
    Generator* g = m->getGenerator();
    VModule* vmod;
    bool hackflag = false;
    if (modMap.count(g)) { //Slightly hacky doing a cache here. I could just preload this with a GeneratorPass
      vmod = modMap[g];
      hackflag = true;
    }
    else {
      vmod = new VModule(g);
      this->modMap[g] = vmod; //Keeping generators in modMap for cache
    }
    this->modMap[m] = vmod;
    if (!vmod->hasDef()) {
      this->external.insert(g);
    }
    else if (!hackflag) {
      modList.push_back(vmod);
    }
    return false;
  }
  VModule* vmod = new VModule(m);
  modMap[m] = vmod;
  if (vmod->hasDef()) {
    ASSERT(!m->hasDef(),"NYI linking error"); //TODO figure out this better
    modList.push_back(vmod);
    return false;
  }
  if (!m->hasDef()) {
    this->external.insert(m);
    return false;
  }
  modList.push_back(vmod);

  ModuleDef* def = m->getDef();
  
  string tab = "  ";
  for (auto imap : def->getInstances()) {
    string iname = imap.first;
    Instance* inst = imap.second;
    Module* mref = imap.second->getModuleRef();
    ASSERT(modMap.count(mref),"DEBUG ME");
    VModule* vref = modMap[mref];
    vmod->addStmt("  //Wire declarations for instance '" + iname + "' (Module "+ vref->getName() + ")");
    for (auto rmap : cast<RecordType>(imap.second->getType())->getRecord()) {
      vmod->addStmt(VWireDec(VWire(iname+"__"+rmap.first,rmap.second)));
    }
    vmod->addStmt(vref->toInstanceString(inst));
  }

  vmod->addStmt("  //All the connections");
  for (auto con : def->getConnections()) {
    vmod->addStmt(VAssign(con));
  }
  
  return false;
}

void Passes::Verilog::writeToStream(std::ostream& os) {
  
  for (auto ext : external) {
    os << modMap[ext]->toCommentString() << endl;
  }
  os << endl;
  for (auto vmod : modList) {
    os << vmod->toString() << endl;
  }

}

Passes::Verilog::~Verilog() {
  set<VModule*> toDelete;
  for (auto m : modMap) {
    toDelete.insert(m.second);
  }
  for (auto m : toDelete) {
    delete m;
  }
}
