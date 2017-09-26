#include "coreir/ir/typegen.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/common.h"
#include "coreir/ir/types.h"

using namespace std;

namespace CoreIR {


Type* TypeGen::getType(Args args) {
  checkArgsAreParams(args,params);
  Type* t = this->createType(ns->getContext(),args);
  return flipped ? t->getFlipped() : t;
}

}
