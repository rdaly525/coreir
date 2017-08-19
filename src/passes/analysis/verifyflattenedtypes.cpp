#include "coreir.h"
#include "coreir-passes/analysis/verifyflattenedtypes.h"

using namespace CoreIR;

string Passes::VerifyFlattenedTypes::ID = "verifyflattenedtypes";
bool Passes::VerifyFlattenedTypes::runOnInstanceGraphNode(InstanceGraphNode& node) {
  ASSERT(0,"NYI");
  return false;
}
