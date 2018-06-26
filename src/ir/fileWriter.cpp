#include <fstream>
#include "coreir/ir/json.h"
#include "coreir/ir/context.h"
#include "coreir/ir/module.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/typegen.h"
#include <unordered_map>
#include <algorithm>
#include <set>
#include "coreir/passes/analysis/coreirjson.h"

using namespace std;
namespace CoreIR {

typedef unordered_map<string,json> jsonmap;

using json = nlohmann::json;

bool endsWith(const string &str, const string &suffix) {
  return ((str.size() >= suffix.size()) &&
            (str.compare(str.size()-suffix.size(), suffix.size(), suffix) == 0));
}
  /*
string instStr(Wireable* wire) {
  Select* child;
  Wireable* parent = wire;

  while (isa<Select>(parent)) {
    child = cast<Select>(parent);
    parent = child->getParent();
  }

  return parent->toString() == "self" ? child->toString() : parent->toString();
}
  */
string instStr(SelectPath wire) {
  if (wire[0] == "self") {
    return wire[0] + "." + wire[1];
  } else {
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

  return parent->toString() == "self" ? child->getSelStr() != "out" 
    : (child ? child->getSelStr() == "out" : false);
}

//false is bad
bool ModuleToDot(Module* m, std::ofstream& stream) {
  Context* c = m->getContext();
  if (!m->hasDef()) {
    Error e;
    e.message("Module " + m->getName() + " is not defined, so cannot be saved to dot file");
    c->error(e);
    return false;
  }

  stream << "digraph Diagram {" << endl
         << "node [shape=box];" << endl;

  DirectedModule* dMod = m->newDirectedModule();
  if (!dMod->getInstances().empty()) {
    for (auto inst : dMod->getInstances()) {
      stream << "\"" 
             << (*inst)->getInstname()
             << "\"; ";
    }
    stream << endl;
    
    if (!dMod->getConnections().empty()) {
      for (auto con : dMod->getConnections()) {
        string src = instStr(con->getSrc());
        string sink = instStr(con->getSnk());

        stream << "\""
               << src
               << "\"";
        stream << "->" ;
        stream << "\""
               << sink
               << "\"; ";
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
  ASSERT(endsWith(filename, ".txt"),filename + "Does not end with .txt");
  // create a txt dot file for use with graphviz
  ModuleToDot(m, file);
  return true;
}

bool saveToFile(Namespace* ns, string filename,Module* top) {
  Context* c = ns->getContext();
  ASSERT(endsWith(filename, ".json"),filename + "Needs to be a json file");
  std::ofstream file(filename);
  if (!file.is_open()) {
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return false;
  }
  
  c->runPasses({"coreirjson"},{ns->getName()});
  auto jpass = static_cast<Passes::CoreIRJson*>(c->getPassManager()->getAnalysisPass("coreirjson"));
  string topRef = "";
  if (top) {
    topRef = top->getNamespace()->getName() + "." + top->getName();
  }
  jpass->writeToStream(file,topRef);
  return true;

}

bool saveToFile(Context* c, string filename, bool nocoreir) {
  ASSERT(endsWith(filename, ".json"),filename + "Needs to be a json file");
  std::ofstream file(filename);
  if (!file.is_open()) {
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return false;
  }
  if (nocoreir) {
    vector<string> nss;
    for (auto nspair : c->getNamespaces()) {
      if (nspair.first!="coreir" && nspair.first!="corebit") {
        nss.push_back(nspair.first);
      }
    }
    c->runPasses({"coreirjson"},nss);
  }
  else {
    c->runPassesOnAll({"coreirjson"});
  }
  auto jpass = static_cast<Passes::CoreIRJson*>(c->getPassManager()->getAnalysisPass("coreirjson"));
  string topRef = "";
  if (c->hasTop()) {
    topRef = c->getTop()->getRefName();
  }
  jpass->writeToStream(file,topRef);
  return true;
}


}//CoreIR namespace
