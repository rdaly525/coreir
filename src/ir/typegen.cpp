#include "typegen.hpp"
#include "namespace.hpp"
#include "common.hpp"
#include "types.hpp"

using namespace std;

namespace CoreIR {


Type* TypeGen::getType(Args args) {
  checkArgsAreParams(args,params);
  Type* t = this->createType(ns->getContext(),args);
  return flipped ? t->getFlipped() : t;
}

}
