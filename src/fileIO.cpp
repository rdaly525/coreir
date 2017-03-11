#ifndef FILEIO_CPP_
#define FILEIO_CPP_

#include "json.hpp"
#include <iostream>
#include <fstream>
#include "context.hpp"
#include "instantiable.hpp"
#include "namespace.hpp"


using json = nlohmann::json;

Module* loadModule(Context* c, string filename, bool* err) {
  std::fstream file;
  file.open(filename);
  if (!file.is_open()) {
    *err =false;
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return nullptr;
  }
  json j;
  file >> j;
  cout << "Loading " << filename << endl;
  cout << "NYI!" << endl;
  return nullptr;
}


//true cannot open file
void saveModule(Module* m, string filename, bool* err) {
  Context* c = m->getContext();
  std::ofstream file(filename);
  if (!file.is_open()) {
    *err =false;
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return;
  }

  //TODO I should gather only the dependent modules
  json j;
  j["top"] = json::array({m->getNamespace()->getName(),m->getName()});
  //for (auto ns: namespaces) jnamespaces[ns->getName()] = ns->toJson();
  j["namespaces"] = {"_G",m->getContext()->getGlobal()->toJson()};
  file << std::setw(3) << j;
  return;
}


json Type::toJson() { 
  return {
    {"type",TypeKind2Str(kind)},
    {"args", "None"}
  };
}
json ArrayType::toJson() {
  return {
    {"type",TypeKind2Str(kind)},
    {"args",json::array({len,elemType->toJson()})}
  };
}
json RecordType::toJson() {
  json jfields;
  for (auto field : record) jfields[field.first] = field.second->toJson();
  return {
    {"type",TypeKind2Str(kind)},
    {"args",jfields}
  };
}

json Namespace::toJson() {
  json jmods;
  json jgens;
  for (auto m : mList) jmods[m.first] = m.second->toJson();
  for (auto g : gList) jgens[g.first] = g.second->toJson();
  return {
    {"modules",jmods},
    {"generators",jgens}
  };
}

json Module::toJson() {
  return {
    {"type",type->toJson()},
    {"config","NYI"},
    {"metadata","NYI"},
    {"def",hasDef() ? getDef()->toJson() : "None"}
  };
}

json ModuleDef::toJson() {
  json j;
  j["metadata"] = "NYI";
  j["implementations"] = "NYI";
  json jinsts;
  for ( auto instmap : instances) {
    jinsts[instmap.first] = instmap.second->toJson();
  }
  j["instances"] = jinsts;
  json jcons;
  for (auto connection : connections) {
    jcons.push_back(connection.toJson());
  }
  j["connections"] = jcons;
  return j;
}

json Connection::toJson() {
  return {
    {"metadata", "NYI"},
    {"connection", json::array({first->toJson(), second->toJson()})}
  };
}

json Wireable::toJson() {
  json j;
  json jpath;
  std::pair<string,vector<string>> path = getPath();
  for (auto str : path.second) jpath.push_back(str);
  j["metadata"] = "NYI";
  jpath["path"] = jpath;
  return j;
}

json Instance::toJson() {
  json j;
  j["instancename"] = instname;
  j["instref"] = json::array({instRef->getNamespace()->getName(),instRef->getName()});
  j["args"] = "NYI";
  j["metadata"] = "NYI";
  return j;
}

json Generator::toJson() {
  return {
    {"genparamter","NYI"},
    {"typegen","NYI"},
    {"metadata","NYI"}
  };
}

#endif //FILEIO_CPP_
