#include "coreir.h"
#include "coreir-passes/analysis/strongverify.h"

using namespace CoreIR;

namespace {
//        Error e;
//        e.message(
//        c->error(e);

bool checkIfFullyConnected(Wireable* w,Error& e) {
  if (w->getConnectedWireables().size()>0) return true;
  if (w->getSelects().size()==0) {
    e.message("{"+w->getContainer()->getName() + "}." + w->toString()+" Is not connected");
    return false;
  }
  if (auto rt = dyn_cast<RecordType>(w->getType())) {
    bool isConnected = true;
    for (auto field : rt->getFields()) {
      if (!w->hasSel(field)) {
        e.message("{"+w->getContainer()->getName() + "}." + w->toString()+"."+field+" Is not fully connected");
        return false;
      }
      isConnected &= checkIfFullyConnected(w->sel(field),e);
    }
    return isConnected;
  }
  else if (auto at = dyn_cast<ArrayType>(w->getType())) {
    bool isConnected = true;
    for (uint i=0; i<at->getLen(); ++i) {
      if (!w->hasSel(to_string(i))) {
        e.message("{"+w->getContainer()->getName() + "}." + w->toString()+"."+to_string(i)+" Is not fully connected");
        return false;
      }
      isConnected &= checkIfFullyConnected(w->sel(i),e);
    }
    return isConnected;
  }
  e.message("{"+w->getContainer()->getName() + "}." + w->toString() + "Is not fully connected");
  return false;
}

}

string Passes::StrongVerify::ID = "strongverify";
bool Passes::StrongVerify::runOnModule(Module* m) {
  //Check if all ports are connected for everything
  if (!m->hasDef()) return false;
  Context* c = this->getContext();
  ModuleDef* def = m->getDef();
  
  Error e;
  bool verify = true;
  verify &= checkIfFullyConnected(def->getInterface(),e);
  for (auto inst : def->getInstances()) {
    verify &= checkIfFullyConnected(inst.second,e);
  }
  if (!verify) {
    e.fatal();
    c->error(e);
  }

  return false;

}
