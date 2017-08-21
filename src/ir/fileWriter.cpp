#include "json.hpp"
#include <fstream>
#include "context.hpp"
#include "instantiable.hpp"
#include "namespace.hpp"
#include "typegen.hpp"
#include <unordered_map>
#include <algorithm>
#include <set>
#include "coreir-passes/analysis/coreirjson.h"

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
//        bool firstIsSource = isSource(conpair.first);
//        string source = firstIsSource ? instStr(conpair.first) : instStr(conpair.second);
//        string sink = firstIsSource ? instStr(conpair.second) : instStr(conpair.first);
        //string source = con->getSrc()
        string src = instStr(con->getSrc());
        string sink = instStr(con->getSnk());
        //assert(src.size() == 1);
        //assert(sink.size() == 1);

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
  ASSERT(endsWith(filename, ".txt"),filename + "Does not end with .txt")
  // create a txt dot file for use with graphviz
  ModuleToDot(m, file);
  return true;
}


bool saveToFilePretty(Namespace* ns, string filename,Module* top) {
  Context* c = ns->getContext();
  ASSERT(endsWith(filename, ".json"),filename + "Needs to be a json file")
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
  return false;

}

//false cannot open file
bool saveToFile(Namespace* ns, string filename,Module* top) {
  

  Context* c = ns->getContext();
  std::ofstream file(filename);
  if (!file.is_open()) {
    Error e;
    e.message("Cannot open file " + filename);
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
  // create a json file
  json j;

  //TODO allow for more namespaces in one file
  j["namespaces"] = json();
  j["namespaces"][ns->getName()] = ns->toJson();
  
  if (top) {
    //for now make sure that top exists in namespace
    if (top->getNamespace() != ns || !ns->hasInstantiable(top->getName())) {
      Error e;
      e.message("Top module does not exit: " + top->getNamespace()->getName() + "." + top->getName());
      e.fatal();
      c->error(e);
      return false;
    }
    j["top"] = top->getNamespace()->getName() + "." + top->getName();
  }
  file << std::setw(2) << j;
  return true;
}

json Args2Json(Args args);
json Params2Json(Params gp);
json Wireable2Json(Wireable* w);

json Type::toJson() { 
  return TypeKind2Str(kind);
}
json ArrayType::toJson() {
  return json::array({TypeKind2Str(kind),len,elemType->toJson()});
}
json RecordType::toJson() {
  json jfields;
  for (auto sel : _order) jfields[sel] = record[sel]->toJson();
  return json::array({TypeKind2Str(kind),jfields});
}

json NamedType::toJson() {
  json j;
  j.push_back("Named");
  j.push_back(ns->getName() + "." + name);
  if (isGen()) {
    j.push_back(Args2Json(genargs));
  }
  return j;
}

json Namespace::toJson() {
  json j;
  if (!moduleList.empty()) {
    json jmods;
    for (auto m : moduleList) jmods[m.first] = m.second->toJson();
    j["modules"] = jmods;
  }
  if (!generatorList.empty()) {
    json jgens;
    for (auto g : generatorList) jgens[g.first] = g.second->toJson();
    j["generators"] = jgens;
  }
  if (!namedTypeNameMap.empty()) {
    json jntypes;
    for (auto nPair : namedTypeNameMap) {
      string n = nPair.first;
      string nFlip = nPair.second;
      NamedType* nt = namedTypeList.at(n);
      Type* raw = nt->getRaw();
      json jntype = {
        {"flippedname",nFlip},
        {"rawtype", raw->toJson()}
      };
      jntypes[n] = jntype;
    }
    j["namedtypes"] = jntypes;
  } 
  if (!typeGenNameMap.empty()) {
    json jntypegens;
    for (auto nPair : typeGenNameMap) {
      string n = nPair.first;
      string nFlip = nPair.second;
      TypeGen* tg = typeGenList.at(n);
      json jntypegen = {
        {"genparams", Params2Json(tg->getParams())}
      };
      if (nFlip != "") {
        jntypegen["flippedname"] = nFlip;
      }
      jntypegens[n] = jntypegen;
    }
    j["namedtypegens"] = jntypegens;
  }
  return j;
}

json Instantiable::toJson() {
  json j;
  if (!configparams.empty()) {
    j["configparams"] = Params2Json(configparams);
  }
  if (!defaultConfigArgs.empty()) {
    j["defaultconfigargs"] = Args2Json(defaultConfigArgs);
  }
  return j;
}

json Module::toJson() {
  json j = Instantiable::toJson();
  j["type"] = type->toJson();
  if (this->hasDef()) {
    json jdef = this->getDef()->toJson();
    if (jdef.count("instances")) {
      j["instances"] = jdef["instances"];
    }
    if (jdef.count("connections")) {
      j["connections"] = jdef["connections"];
    }
  }
  return j;
}

json Generator::toJson() {
  json j = Instantiable::toJson();
  j["genparams"] = Params2Json(genparams);
  if (!defaultGenArgs.empty()) {
    j["defaultgenargs"] = Args2Json(defaultGenArgs);
  }
  //You need to add namespace back to typegen (ugh)
  j["typegen"] = json::array({typegen->getNamespace()->getName(),typegen->getName()});
  return j;
}

json Connection2Json(Connection con) {
  auto pa = con.first->getSelectPath();
  auto pb = con.second->getSelectPath();
  string sa = join(pa.begin(),pa.end(),string("."));
  string sb = join(pb.begin(),pb.end(),string("."));
  return json::array({sa,sb});
}

json ModuleDef::toJson() {
  json j;
  if (!instances.empty()) {
    json jinsts;
    for ( auto instmap : instances) {
      jinsts[instmap.first] = instmap.second->toJson();
    }
    j["instances"] = jinsts;
  }
  if (!connections.empty()) {
    json jcons;
    std::set<Connection,ConnectionComp> sortedSet(connections.begin(),connections.end());
    for (auto con : sortedSet) {
      jcons.push_back(Connection2Json(con));
    }
    j["connections"] = jcons;
  }
  return j;
}

json Instance::toJson() {
  json j;
  if (this->isGen()) {
    j["genref"] = generatorRef->getNamespace()->getName() + "." + generatorRef->getName();
    j["genargs"] = Args2Json(genargs);
  }
  else {
    j["modref"] = moduleRef->getNamespace()->getName() + "." + moduleRef->getName();
  }
  if (this->hasConfigArgs()) {
    j["configargs"] = Args2Json(this->getConfigArgs());
  }
  return j;
}

json Params2Json(Params gp) {
  json j = {};
  for (auto it : gp) j[it.first] = Param2Str(it.second);
  return j;
}

json Args2Json(Args args) {
  json j;
  for (auto it : args) j[it.first] = it.second->toJson();
  return j;
}

json ArgString::toJson() { return str; }
json ArgInt::toJson() { return i; }
json ArgBool::toJson() { return b; }
json ArgType::toJson() { return t->toJson(); }

}//CoreIR namespace
