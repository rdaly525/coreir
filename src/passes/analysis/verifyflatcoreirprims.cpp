#include "coreir.h"
#include "coreir/passes/analysis/verifyflatcoreirprims.h"

using namespace CoreIR;
using namespace std;

string Passes::VerifyFlatCoreirPrims::ID = "verifyflatcoreirprims";
bool Passes::VerifyFlatCoreirPrims::runOnInstanceGraphNode(InstanceGraphNode & node) {
  // check that all instances are coreir primitives
  Namespace* coreir = this->getContext()->getNamespace("coreir");
  Namespace* corebit = this->getContext()->getNamespace("corebit");
  Namespace* mantle = this->getContext()->getNamespace("mantle");
  Namespace* ns;
  for (auto inst : node.getInstanceList()) {
    Module *m = inst->getModuleRef();
    if (m->isGenerated()) {
      ns = m->getGenerator()->getNamespace();
        }
    else {
      ns = m->getNamespace();
        }
    ASSERT(ns == coreir || ns == corebit || ns == mantle, "Expected flattened design and {" + inst->getInstname() + ", namespace= " + ns->getName() + "} is not a recognized primitive.");
  }
  return false;
}
