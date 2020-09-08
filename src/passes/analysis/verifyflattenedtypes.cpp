#include "coreir/passes/analysis/verifyflattenedtypes.h"
#include "coreir.h"
#include "coreir/tools/cxxopts.h"

using namespace std;
using namespace CoreIR;

bool Passes::VerifyFlattenedTypes::check(Type* t) {
  if (this->allow_ndarrays) { return isBitOrNDArrOfBits(t); }
  return isBitOrArrOfBits(t);
}

bool Passes::VerifyFlattenedTypes::runOnInstanceGraphNode(
  InstanceGraphNode& node) {

  Module* m = node.getModule();
  for (auto rpair : m->getType()->getRecord()) {
    ASSERT(
      this->check(rpair.second),
      "{" + m->getRefName() + "}." + rpair.first +
        " Is not a flattened type!\n  Type is: " + rpair.second->toString());
  }

  return false;

  // Module* m = node.getModule();
  // if (isa<Generator>(i)) {
  //  //Check all instances of generator
  //  for (auto inst : node.getInstanceList()) {
  //    for (auto rmap : (cast<RecordType>(inst->getType()))->getRecord()) {
  //      ASSERT(isBitOrArrOfBits(rmap.second),
  //        "{"+inst->getContainer()->getModule()->getRefName()+"}."+inst->getInstname()
  //        + "." + rmap.first + " IS not flattened!\n  Type is: " +
  //        rmap.second->toString());
  //    }
  //  }
  //}
  // else {
  //  //Just check the interface of the module
  //  Module* m = cast<Module>(i);
  //  RecordType* rt = cast<RecordType>(m->getType());
  //  for (auto rmap : rt->getRecord()) {
  //    ASSERT(isBitOrArrOfBits(rmap.second),"{"+m->getRefName()+"}."+rmap.first+"
  //    is not flattened!\n  Type is: " + rmap.second->toString());
  //  }
  //}
  //
  // return false;
}

void Passes::VerifyFlattenedTypes::initialize(int argc, char** argv) {
  cxxopts::Options options(
    "verifyflattentypes",
    "Checks that all types have beeen flattened");
  options.add_options()(
    "n,ndarray",
    "Allow multi-dimensional array of bits (ndarrays)");
  auto opts = options.parse(argc, argv);
  if (opts.count("n")) { this->allow_ndarrays = true; }
}
