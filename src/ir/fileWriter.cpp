#include <algorithm>
#include <fstream>
#include <set>
#include <unordered_map>
#include "coreir/ir/context.h"
#include "coreir/ir/json.h"
#include "coreir/ir/module.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/typegen.h"
#include "coreir/passes/analysis/coreirjson.h"

using namespace std;
namespace CoreIR {

typedef unordered_map<string, json> jsonmap;

using json = nlohmann::json;

bool endsWith(const string& str, const string& suffix) {
  return (
    (str.size() >= suffix.size()) &&
    (str.compare(str.size() - suffix.size(), suffix.size(), suffix) == 0));
}

string instStr(SelectPath wire) {
  if (wire[0] == "self") { return wire[0] + "." + wire[1]; }
  else {
    return wire[0];
  }
}

bool isSource(Wireable* wire) {
  Select* child;
  Wireable* parent = wire;

  while (isa<Select>(parent)) {
    child = cast<Select>(parent);
    parent = child->getParent();
  }

  return parent->toString() == "self"
    ? child->getSelStr() != "out"
    : (child ? child->getSelStr() == "out" : false);
}

// false is bad
bool ModuleToDot(Module* m, std::ostream& stream) {
  Context* c = m->getContext();
  if (!m->hasDef()) {
    Error e;
    e.message(
      "Module " + m->getName() +
      " is not defined, so cannot be saved to dot file");
    c->error(e);
    return false;
  }

  stream << "digraph Diagram {" << endl << "node [shape=box];" << endl;

  DirectedModule* dMod = m->newDirectedModule();
  if (!dMod->getInstances().empty()) {
    for (auto inst : dMod->getInstances()) {
      string moduleName = (*inst)->getModuleRef()->getName();
      string displayName = moduleName;
      if (moduleName == "PE") {
        if ((*inst)->getModArgs().count("alu_op") > 0) {
          displayName = (*inst)->getModArgs().at("alu_op")->get<string>();
        } else if ((*inst)->getModArgs().count("lut_value") > 0) {
          auto lutValue = (*inst)->getModArgs().at("lut_value")->get<BitVector>();
          displayName = "LUT: " + lutValue.hex_string();
        }
      } else if (moduleName == "reg") {
        displayName = "__/\\\\__";
          
      } else if (moduleName == "const") {
        if ((*inst)->getModArgs().count("value") > 0) {
          auto bv = (*inst)->getModArgs().at("value")->get<BitVector>();
          displayName += ": " + bv.hex_string();
        }
      }
      stream << "\"" << (*inst)->getInstname() << "\" [label=\"" << displayName << "\"]; ";
    }
    stream << endl;

    if (!dMod->getConnections().empty()) {
      for (auto con : dMod->getConnections()) {
        string src = instStr(con->getSrc());
        string sink = instStr(con->getSnk());

        stream << "\"" << src << "\"";
        stream << "->";
        stream << "\"" << sink << "\"; ";
      }
      stream << endl;
    }
  }

  stream << "}" << endl;
  return true;
}

bool saveToDot(Module* m, string filename) {
  Context* c = m->getContext();
  std::ofstream file(filename);
  if (!file.is_open()) {
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return false;
  }
  ASSERT(endsWith(filename, ".txt"), filename + "Does not end with .txt");
  return saveToDot(m, file);
}

bool saveToDot(Module* m, std::ostream& fout) {
  // create a txt dot file for use with graphviz
  return ModuleToDot(m, fout);
}

bool saveToFile(Namespace* ns, string filename, Module* top) {
  Context* c = ns->getContext();
  ASSERT(endsWith(filename, ".json"), filename + "Needs to be a json file");
  std::ofstream file(filename);
  if (!file.is_open()) {
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return false;
  }

  c->runPasses({"coreirjson"}, {ns->getName()});
  auto jpass = static_cast<Passes::CoreIRJson*>(
    c->getPassManager()->getAnalysisPass("coreirjson"));
  string topRef = "";
  if (top) { topRef = top->getNamespace()->getName() + "." + top->getName(); }
  jpass->writeToStream(file, topRef);
  return true;
}

// Allows user to skip code generation of namespaces that are loaded by default
// as coreir "standard libraries".  This cleans up the generated JSON to contain
// only the user-defined modules
bool skip_namespace(std::string name, bool nocoreir, bool no_default_libs) {
  if (nocoreir && (name == "coreir" || name == "corebit")) { return true; }
  else if (
    no_default_libs &&
    (name == "mantle" || name == "commonlib" || name == "memory" ||
     name == "ice40")) {
    return true;
  }
  return false;
}


bool saveToFile(
  Context* c,
  string filename,
  bool nocoreir,
  bool no_default_libs) {
  ASSERT(endsWith(filename, ".json"), filename + "Needs to be a json file");
  std::ofstream file(filename);
  if (!file.is_open()) {
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return false;
  }
  if (no_default_libs) { nocoreir = true; }
  if (nocoreir || no_default_libs) {
    vector<string> nss;
    for (auto nspair : c->getNamespaces()) {
      if (!skip_namespace(nspair.first, nocoreir, no_default_libs)) {
        nss.push_back(nspair.first);
      }
    }
    c->runPasses({"coreirjson"}, nss);
  }
  else {
    c->runPassesOnAll({"coreirjson"});
  }
  static_cast<Passes::CoreIRJson*>(
    c->getPassManager()->getAnalysisPass("coreirjson"))
    ->writeToStream(file);
  return true;
}

bool serializeToFile(Context* c, string filename) {
  if (!c->hasTop()) {
    Error e;
    e.message("Missing Top " + filename);
    e.fatal();
    c->error(e);
    return false;
  }
  if (!endsWith(filename, ".json")) {
    Error e;
    e.message(filename + "Needs to be a json file");
    e.fatal();
    c->error(e);
    return false;
  }

  std::ofstream file(filename);
  if (!file.is_open()) {
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return false;
  }
  c->runPasses({"serialize --top"});
  static_cast<Passes::CoreIRSerialize*>(
    c->getPassManager()->getAnalysisPass("serialize"))
    ->writeToStream(file);
  return true;
}

bool serializeHeader(Context*c, std::string filename, std::vector<std::string> modules) {
  ASSERT(endsWith(filename, ".json"), filename + "Needs to be a json file");
  std::ofstream file(filename);
  if (!file.is_open()) {
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return false;
  }
  std::string serialize_cmd = "serialize --header --modules " + join(modules.begin(), modules.end(), std::string(","));
  c->runPasses({serialize_cmd});
  static_cast<Passes::CoreIRSerialize*>(
    c->getPassManager()->getAnalysisPass("serialize"))
    ->writeToStream(file);
  return true;
}


bool serializeDefinitions(Context*c, std::string filename, std::vector<std::string> modules) {
  ASSERT(endsWith(filename, ".json"), filename + "Needs to be a json file");
  std::ofstream file(filename);
  if (!file.is_open()) {
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return false;
  }
  std::string serialize_cmd = "serialize --modules " + join(modules.begin(), modules.end(), std::string(","));
  c->runPasses({serialize_cmd});
  static_cast<Passes::CoreIRSerialize*>(
    c->getPassManager()->getAnalysisPass("serialize"))
    ->writeToStream(file);
  return true;
}



}  // namespace CoreIR
