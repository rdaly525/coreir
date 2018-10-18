#include "coreir/ir/globalvalue.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/common.h"

using namespace std;
namespace CoreIR {

GlobalValue::GlobalValue(GlobalValueKind kind, Namespace* ns, std::string name) : MetaData(), kind(kind), ns(ns), name(name) {
  checkStringSyntax(name);
}
string GlobalValue::getRefName() const {
  return this->ns->getName() + "." + this->name;
}

Context* GlobalValue::getContext() {
  return ns->getContext();
}

}
