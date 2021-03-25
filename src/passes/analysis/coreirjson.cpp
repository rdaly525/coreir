#include "coreir/passes/analysis/coreirjson.h"
#include <map>
#include "coreir.h"
#include "coreir/passes/analysis/coreir_json_lib.h"

using namespace CoreIR;
using namespace CoreIR::JsonLib;
using namespace std;

bool Passes::CoreIRJson::runOnNamespace(Namespace* ns) {
  auto modlist = ns->getModules(false);
  if (
    ns->getGenerators().empty() && ns->getTypeGens().empty() &&
    modlist.empty()) {
    // Skip if empty
    return false;
  }
  nsMap[ns->getName()] = ns2Json(ns);
  return false;
}

void Passes::CoreIRJson::writeToStream(std::ostream& os, string topRef) {
  os << "{";
  if (topRef != "") { os << quote("top") << ":" << quote(topRef) << ","; }
  os << endl;
  Dict jn(0);
  for (auto nmap : nsMap) { jn.add(nmap.first, nmap.second); }
  os << quote("namespaces") << ":" << jn.toMultiString();
  os << endl << "}" << endl;
}

void Passes::CoreIRJson::writeToStream(std::ostream& os) {
  std::string top = "";
  Context* c = this->getContext();
  if (c->hasTop()) { top = c->getTop()->getRefName(); };
  return Passes::CoreIRJson::writeToStream(os, top);
}
