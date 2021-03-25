#include <map>
#include "coreir.h"
#include "coreir/passes/analysis/coreir_json_lib.h"
#include "coreir/passes/analysis/coreirjson.h"

using namespace CoreIR;
using namespace CoreIR::JsonLib;
using namespace std;

NamespaceJson& Passes::CoreIRSerialize::getOrCreateNamespace(Namespace* ns) {
  if (this->nss.count(ns->getName()) == 0) {
    this->nss.emplace(ns->getName(), ns);
  }
  return this->nss.at(ns->getName());
}

bool Passes::CoreIRSerialize::runOnInstanceGraphNode(InstanceGraphNode& node) {
  auto m = node.getModule();
  auto ns = m->getNamespace();

  this->getOrCreateNamespace(ns).add_module(m);

  // Typegens may be in another namespace
  if (m->isGenerated()) {
    auto tg = m->getGenerator()->getTypeGen();
    auto tg_ns = tg->getNamespace();
    this->getOrCreateNamespace(tg_ns).add_typegen(tg);
  }
  return false;
}

void Passes::CoreIRSerialize::writeToStream(std::ostream& os) {
  auto c = this->getContext();
  ASSERT(c->hasTop(), "Cannot Serialize a circuit with no Top");
  os << "{";
  os << quote("top") << ":" << quote(c->getTop()->getRefName()) << ",";
  os << endl;
  Dict jn(0);
  for (auto &[nsname, nsjson] : this->nss) { jn.add(nsname, nsjson.serialize()); }
  os << quote("namespaces") << ":" << jn.toMultiString();
  os << endl << "}" << endl;
}

