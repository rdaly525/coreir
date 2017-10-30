#include "coreir/ir/globalvalue.h"
#include "coreir/ir/namespace.h"

using namespace std;
namespace CoreIR {

string GlobalValue::getRefName() const {
  return this->ns->getName() + "." + this->name;
}

Context* GlobalValue::getContext() {
  return ns->getContext();
}

}
