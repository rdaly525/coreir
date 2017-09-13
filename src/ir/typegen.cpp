#include "coreir/ir/typegen.hpp"
#include "coreir/ir/namespace.hpp"
#include "coreir/ir/common.hpp"
#include "coreir/ir/types.hpp"

using namespace std;

namespace CoreIR {


Type* TypeGen::getType(Args args) {
  checkArgsAreParams(args,params);
  Type* t = this->createType(ns->getContext(),args);
  return flipped ? t->getFlipped() : t;
}

}
