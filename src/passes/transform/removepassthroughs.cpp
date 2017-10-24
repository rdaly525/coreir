
#include "coreir.h"
#include "coreir/passes/transform/removepassthroughs.h"

using namespace CoreIR;

namespace {

  bool inlinePassthrough(Instance* inst) {
    return inlineInstance(inst);
  }

}


std::string Passes::RemovePassthroughs::ID = "removepassthroughs";

void Passes::RemovePassthroughs::setVisitorInfo() {
//Context* c = this->getContext();
  addVisitorFunction(c->getInstantiable("mantle.wire"),inlinePassthrough);

}
