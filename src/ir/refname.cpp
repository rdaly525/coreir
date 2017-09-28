#include "coreir/ir/refname.h"
#include "coreir/ir/namespace.h"

using namespace std;
namespace CoreIR {

string RefName::getRefName() const {
  return this->ns->getName() + "." + this->name;
}

Context* RefName::getContext() {
  return c;
}

}
