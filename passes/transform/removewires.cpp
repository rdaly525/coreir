
#include "passes/transform/removewires.h"
#include "ir/coreir.h"

using namespace CoreIR;

namespace {

bool inlineWire(Instance* inst) { return inlineInstance(inst); }

}  // namespace

std::string Passes::RemoveWires::ID = "removewires";

void Passes::RemoveWires::setVisitorInfo() {
  addVisitorFunction(getContext()->getGenerator("mantle.wire"), inlineWire);
  addVisitorFunction(getContext()->getGenerator("coreir.wire"), inlineWire);
  addVisitorFunction(getContext()->getModule("corebit.wire"), inlineWire);
}