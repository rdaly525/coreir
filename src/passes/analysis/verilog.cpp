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
  if (auto g = dyn_cast<Generator>(i)) {
    auto vmod = new VModule(g);
    this->modMap[i] = vmod;
    if (!vmod->hasDef()) {
      this->external.insert(i);
    }
    return false;
  }
  Module* m = cast<Module>(i);
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
    Instantiable* iref = imap.second->getInstantiableRef();
    vmod->addStmt("  //Wire declarations for instance '" + imap.first + "' (Module "+ iref->getName() + ")");
    for (auto rmap : cast<RecordType>(imap.second->getType())->getRecord()) {
      vmod->addStmt(VWireDec(VWire(iname+"_"+rmap.first,rmap.second)));
    }
    ASSERT(modMap.count(iref),"DEBUG ME: Missing iref");
    vmod->addStmt(modMap[iref]->toInstanceString(inst));
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
