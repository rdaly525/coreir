#include <map>
#include "coreir.h"
#include "coreir/passes/analysis/coreir_json_lib.h"
#include "coreir/passes/analysis/coreirjson.h"
#include "coreir/tools/cxxopts.h"

using namespace CoreIR;
using namespace CoreIR::JsonLib;
using namespace std;

void Passes::CoreIRSerialize::initialize(int argc, char** argv) {
  cxxopts::Options options("serialize", "serializes CoreIR");
  options.add_options()("m,modules", "serializes the list of modules and their deps", cxxopts::value<std::string>())("t,top", "Serializes top")("h,header", "Serializes only the module declarations");

  auto opts = options.parse(argc, argv);
  if (opts.count("t") > 0) {
    this->onlyTop = true;
  }
  else if (opts.count("m")) {
    auto mods_string = opts["m"].as<std::string>();
    auto mods = splitString<vector<string>>(mods_string, ',');
    for (auto m : mods) {
      this->modules.push_back(m);
    }
  }
  if (opts.count("h")) {
    this->headerOnly=true;
  }
}

void Passes::CoreIRSerialize::releaseMemory() {
  this->onlyTop = false;
  this->modules.clear();
  this->headerOnly=false;
}

NamespaceJson& Passes::CoreIRSerialize::getOrCreateNamespace(Namespace* ns) {
  if (this->nss.count(ns->getName()) == 0) {
    this->nss.emplace(ns->getName(), ns);
  }
  return this->nss.at(ns->getName());
}

bool Passes::CoreIRSerialize::runOnInstanceGraphNode(InstanceGraphNode& node) {

  //Skip if it is header only and this module is not one of the specified modules
  if (this->headerOnly) {
    auto mref = node.getModule()->getRefName();
    if (!std::count(this->modules.begin(), this->modules.end(), mref)) {
      return false;
    }
  }

  auto m = node.getModule();
  auto ns = m->getNamespace();

  this->getOrCreateNamespace(ns).add_module(m, this->headerOnly);

  // Typegens may be in another namespace
  if (m->isGenerated()) {
    auto tg = m->getGenerator()->getTypeGen();
    auto tg_ns = tg->getNamespace();
    auto& tgjson = this->getOrCreateNamespace(tg_ns).getOrCreateTypeGen(tg);
    tgjson.add_type(m->getGenArgs(), m->getType());
  }
  return false;
}

void Passes::CoreIRSerialize::writeToStream(std::ostream& os) {
  auto c = this->getContext();
  ASSERT(!this->onlyTop || c->hasTop(), "Cannot Serialize a circuit with no Top");
  os << "{";
  if (this->onlyTop) {
    os << quote("top") << ":" << quote(c->getTop()->getRefName()) << ",";
    os << endl;
  }
  Dict jn(0);
  for (auto &[nsname, nsjson] : this->nss) { jn.add(nsname, nsjson.serialize()); }
  os << quote("namespaces") << ":" << jn.toMultiString();
  os << endl << "}" << endl;
}

