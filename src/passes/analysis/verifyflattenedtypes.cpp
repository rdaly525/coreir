#include "coreir.h"
#include "coreir/passes/analysis/verifyflattenedtypes.h"

using namespace std;
using namespace CoreIR;

namespace {
inline bool isBit(Type* t) {
  return t->isBaseType() || isa<NamedType>(t);
}
bool isBitOrArrOfBits(Type* t) {
  if (isBit(t)) return true;
  if (auto at = dyn_cast<ArrayType>(t)) {
    return isBit(at->getElemType());
  }
  return false;
}
}

string Passes::VerifyFlattenedTypes::ID = "verifyflattenedtypes";
bool Passes::VerifyFlattenedTypes::runOnInstanceGraphNode(InstanceGraphNode& node) {
  
  Module* m = node.getModule();
  for (auto rpair : m->getType()->getRecord()) {
    ASSERT(isBitOrArrOfBits(rpair.second),
      "{"+m->getRefName()+"}."+rpair.first + " Is not a flattened type!\n  Type is: " + rpair.second->toString()); 
  }

  return false;


  //Module* m = node.getModule();
  //if (isa<Generator>(i)) {
  //  //Check all instances of generator
  //  for (auto inst : node.getInstanceList()) {
  //    for (auto rmap : (cast<RecordType>(inst->getType()))->getRecord()) {
  //      ASSERT(isBitOrArrOfBits(rmap.second),
  //        "{"+inst->getContainer()->getModule()->getRefName()+"}."+inst->getInstname() + "." + rmap.first + " IS not flattened!\n  Type is: " + rmap.second->toString()); 
  //    }
  //  }
  //}
  //else {
  //  //Just check the interface of the module
  //  Module* m = cast<Module>(i);
  //  RecordType* rt = cast<RecordType>(m->getType());
  //  for (auto rmap : rt->getRecord()) {
  //    ASSERT(isBitOrArrOfBits(rmap.second),"{"+m->getRefName()+"}."+rmap.first+" is not flattened!\n  Type is: " + rmap.second->toString()); 
  //  }
  //}
  //
  //return false;
}
