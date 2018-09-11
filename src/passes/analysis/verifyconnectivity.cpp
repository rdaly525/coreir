#include "coreir.h"
#include "coreir/passes/analysis/verifyconnectivity.h"

using namespace std;
using namespace CoreIR;

bool Passes::VerifyConnectivity::checkIfFullyConnected(Wireable* w,Error& e) {
  if (this->onlyInputs && w->getType()->isOutput()) {
    return true;
  }
  if (auto rt = dyn_cast<RecordType>(w->getType())) {
    if (rt->getRecord().size()==0) return true;
  }

  Context* c = this->getContext();
  if (w->getConnectedWireables().size()>0) return true;
  if (auto nt = dyn_cast<NamedType>(w->getType())) {
    bool crin = nt == c->Named("coreir.clkIn") || nt == c->Named("coreir.arstIn");
    bool crout = nt == c->Named("coreir.clk") || nt == c->Named("coreir.arst");
    if (!this->checkClkRst && (crin || (!this->onlyInputs && crout))) {
      return true;
    }
    e.message("{"+w->getContainer()->getName() + "}." + w->toString()+" Is not fully connected (N)");
    return false;
  }
  if (w->getSelects().size()==0) {
    w->getContainer()->print();
    e.message("{"+w->getContainer()->getName() + "}." + w->toString()+" Is not connected");
    if (w->getContainer()->getModule()->isGenerated()) {
      e.message("with params=" + toString(w->getContainer()->getModule()->getGenArgs()));
    }
    e.fatal();
    w->getContext()->error(e);
    return false;
  }
  if (auto rt = dyn_cast<RecordType>(w->getType())) {
    bool isConnected = true;
    for (auto field : rt->getFields()) {
      isConnected &= checkIfFullyConnected(w->sel(field),e);
    }
    if (!isConnected) {
      e.message("{"+w->getContainer()->getName() + "}." + w->toString()+" Is not fully connected (R)");
    }
    return isConnected;
  }
  else if (auto at = dyn_cast<ArrayType>(w->getType())) {
    bool isConnected = true;
    for (uint i=0; i<at->getLen(); ++i) {
      //TODO bug with named types here
      if (!w->canSel(to_string(i))) {
        e.message("{"+w->getContainer()->getName() + "}." + w->toString()+"."+to_string(i)+" Is not fully connected (A)");
        return false;
      }
      isConnected &= checkIfFullyConnected(w->sel(i),e);
    }
    return isConnected;
  }
  else {
    ASSERT(0,"CANNOT HANDLE TYPE: " + w->getType()->toString());
    return false;
  }
}

string Passes::VerifyConnectivity::ID = "verifyconnectivity";
bool Passes::VerifyConnectivity::runOnModule(Module* m) {
  //Check if all ports are connected for everything
  Context* c = this->getContext();
  ModuleDef* def = m->getDef();
  
  Error e;
  bool verify = true;
  verify &= checkIfFullyConnected(def->getInterface(),e);
  for (auto inst : def->getInstances()) {
    verify &= checkIfFullyConnected(inst.second,e);
  }
  if (!verify) {
    c->error(e);
    c->printerrors();
  }
  return false;

}
