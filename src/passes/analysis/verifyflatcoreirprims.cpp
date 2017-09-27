#include "coreir.h"
#include "coreir/passes/analysis/verifyflatcoreirprims.h"

using namespace CoreIR;
using namespace std;

string Passes::VerifyFlatCoreirPrims::ID = "verifyflatcoreirprims";
bool Passes::VerifyFlatCoreirPrims::runOnInstanceGraphNode(InstanceGraphNode & node) {
	// check that all instances are coreir primitives
	Namespace* coreir = this->getContext()->getNamespace("coreir");
	for (auto inst : node.getInstanceList()) {
		if (inst->isGen()) {
			ASSERT(inst->getGeneratorRef()->getNamespace() == coreir, "Expected flattened design and {" + inst->getInstname() + "} is not a coreir primitive.")
		}
		else {
			ASSERT(inst->getModuleRef()->getNamespace() == coreir, "Expected flattened design and {" + inst->getInstname() + "} is not a coreir primitive.")
		}
	}
	return false;
}
