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
  Instantiable* i = node.getInstantiable();
  Module* m = cast<Module>(i);
  if (m->generated() && !m->hasDef()) {
    Generator* g = m->getGenerator();
    VModule* vmod;
    if (modMap.count(g)) {
      vmod = modMap[g];
    }
    else {
      vmod = new VModule(g);
    }
    this->modMap[i] = vmod;
    if (!vmod->hasDef()) {
      this->external.insert(g);
    }
    return false;
  }
  VModule* vmod = new VModule(m);
  modMap[i] = vmod;
  if (vmod->hasDef()) {
    ASSERT(!m->hasDef(),"Overriding coreir def with verilog def"); //TODO figure out this better
    return false;
  }
  if (!m->hasDef()) {
    this->external.insert(i);
    return false;
  }

  ModuleDef* def = m->getDef();
  
  string tab = "  ";
  for (auto imap : def->getInstances()) {
    string iname = imap.first;
    Instance* inst = imap.second;
    Module* mref = imap.second->getModuleRef();
    ASSERT(modMap.count(mref),"DEBUG FUCK");
    VModule* vref = modMap[mref];
    vmod->addStmt("  //Wire declarations for instance '" + iname + "' (Module "+ vref->getName() + ")");
    for (auto rmap : cast<RecordType>(imap.second->getType())->getRecord()) {
      vmod->addStmt(VWireDec(VWire(iname+"_"+rmap.first,rmap.second)));
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
  for (auto mmap : modMap) {
    if (external.count(mmap.first)==0) { 
      os << mmap.second->toString() << endl;
    }
  }


}
