#include "coreir.h"
#include "coreir/passes/analysis/verifyflatcoreirprims.h"

using namespace CoreIR;
using namespace std;

string Passes::VerifyFlatCoreirPrims::ID = "verifyflatcoreirprims";
bool Passes::VerifyFlatCoreirPrims::runOnInstanceGraphNode(InstanceGraphNode & node) {
  // check that all instances are coreir primitives
  Namespace* coreir = this->getContext()->getNamespace("coreir");
  for (auto inst : node.getInstanceList()) {
    Module *m = inst->getModuleRef();
    if (m->isGenerated()) {
      ASSERT(m->getGenerator()->getNamespace() == coreir, "Expected flattened design and {" + inst->getInstname() + "} is not a coreir primitive.")
        }
    else {
      ASSERT(m->getNamespace() == coreir, "Expected flattened design and {" + inst->getInstname() + "} is not a coreir primitive.")
        }
  }
  return false;
}
