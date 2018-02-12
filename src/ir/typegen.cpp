#include "coreir/ir/typegen.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/common.h"
#include "coreir/ir/types.h"
#include "coreir/ir/value.h"

using namespace std;

namespace CoreIR {


Type* TypeGen::getType(Values args) {
  checkValuesAreParams(args,params);
  try {
    Type* t = this->createType(ns->getContext(),args);
    return flipped ? t->getFlipped() : t;
  }
  catch(std::out_of_range) {
    cout << "Failed on " << this->getRefName() << " with args=" << ::CoreIR::toString(args) << endl;
    assert(0);
    return nullptr;
  }
}

}
