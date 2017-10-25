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
  if (m->generated() && !m->hasDef()) { //TODO linking concern
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
    this->modMap[i] = vmod;
    if (!vmod->hasDef()) {
      this->external.insert(g);
    }
    else if (!hackflag) {
      modList.push_back(vmod);
    }
    return false;
  }
  VModule* vmod = new VModule(m);
  modMap[i] = vmod;
  modList.push_back(vmod);
  if (vmod->hasDef()) {
    ASSERT(!m->hasDef(),"NYI linking error"); //TODO figure out this better
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
    ASSERT(modMap.count(mref),"DEBUG ME");
    VModule* vref = modMap[mref];
    vmod->addStmt("  //Wire declarations for instance '" + iname + "' (Module "+ vref->getName() + ")");
    for (auto rmap : cast<RecordType>(imap.second->getType())->getRecord()) {
      vmod->addStmt(VWireDec(VWire(iname+"_"+rmap.first,rmap.second)));
    }
// <<<<<<< HEAD
//     ASSERT(modMap.count(iref),"DEBUG ME: Missing iref");

//     cout << "Calling toInstanceString() for " << inst->toString() << endl;

//     vmod->addStmt(modMap[iref]->toInstanceString(inst));
// =======
    vmod->addStmt(vref->toInstanceString(inst));
    //>>>>>>> upstream/dev
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
