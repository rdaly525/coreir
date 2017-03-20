#ifndef FILEIO_CPP_
#define FILEIO_CPP_

#include "json.hpp"
#include <iostream>
#include <fstream>
#include "context.hpp"
#include "instantiable.hpp"
#include "namespace.hpp"
#include <unordered_map>

namespace CoreIR {

typedef unordered_map<string,json> jsonmap;

using json = nlohmann::json;

Type* json2Type(Context* c, json jt);
Args json2Args(Context* c, Params p, json j);
Params json2Params(Context* c, json j);

Instantiable* getSymbol(Context* c, string nsname, string iname);

Module* loadModule(Context* c, string filename, bool* err) {
  std::fstream file;
  file.open(filename);
  if (!file.is_open()) {
    *err =true;
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return nullptr;
  }
  json j;
  file >> j;
  Module* mod = nullptr;

  //TODO add in a JSON parse exception
  try {
    string topnsname = j.at("top").at(0);
    string topmodname = j.at("top").at(1);
    
    //First load all the module declarations
    vector<std::pair<Module*,json>> modqueue;
    //Get or create namespace
    for (auto jnsmap : j.at("namespaces").get<jsonmap>() ) {
      string nsname = jnsmap.first;
      json jns = jnsmap.second;
      Namespace* ns;
      if (c->hasNamespace(nsname) ) ns = c->getNamespace(topnsname);
      else ns = c->newNamespace(topnsname);
      //Load Modules
      for (auto jmodmap : jns.at("modules").get<jsonmap>()) {
        //Figure out type;
        string jmodname = jmodmap.first;
        json jmod = jmodmap.second;
        //cout << "FOR mod: " << jmodname << endl;
        //cout << std::setw(1) << jmod;
        Type* t = json2Type(c,jmod.at("type"));
        Params configparams = json2Params(c,jmod.at("configparams"));
        Module* m = ns->newModuleDecl(jmodname,t,configparams);
        modqueue.push_back({m,jmod});
      }
      //TODO Load Generators
    }

    //Now do all the ModuleDefinitions
    for (auto mq : modqueue) {
      Module* m = mq.first;
      json jmod = mq.second;
      // TODO Module metadata
      json jdef = jmod.at("def");
      if (jdef.is_null()) {
        continue;
      }
      
      ModuleDef* mdef = m->newModuleDef();
      // TODO ModuleDef metadata
      // TODO moduledef implementations
      for (auto jinstmap : jdef.at("instances").get<jsonmap>()) {
        string instname = jinstmap.first;
        json jinst = jinstmap.second;
        json jinstRef = jinst.at("instref");
        
        // This function can throw an error
        Instantiable* instRef = getSymbol(c,jinstRef.at(0),jinstRef.at(1));
        
        Args config = json2Args(c,instRef->getConfigParams(),jinst.at("config"));
        //Assume that if there are args, it is a generator
        if (jinst.at("genargs").is_null()) { // This is a module
          assert(instRef->isKind(MOD));
          mdef->addInstance(instname,(Module*) instRef,config);
        }
        else { // This is a generator
          cout << "NYI Generator instances: " << instname << endl;
          assert(instRef->isKind(GEN));
          assert(false);
        }
      } // End Instances
      //Connections
      if (!jdef.at("connections").is_null()) {
        for (auto jcon : jdef.at("connections").get<vector<vector<json>>>()) {
          //TODO connection metadata
          json wA = jcon[0].get<jsonmap>();
          json wB = jcon[1].get<jsonmap>();
          json jpairA = wA.at("path").get<vector<json>>();
          json jpairB = wB.at("path").get<vector<json>>();

          //std::pair<string,json> jpair = wA.path.get<std::pair<string,json>>();
          //WirePath path = {jpair.first,jpair.second.get<vector<string>>()};
          WirePath pathA = {jpairA[0].get<string>(),jpairA[1].get<vector<string>>()};
          WirePath pathB = {jpairB[0].get<string>(),jpairB[1].get<vector<string>>()};
          mdef->wire(pathA,pathB);
        }
      }
      
      //Add Def back in
      m->addDef(mdef);
    } //End Module loop
    
    //Reference Top
    Instantiable* topInst = getSymbol(c,topnsname,topmodname);
    assert(topInst->isKind(MOD));
    mod = (Module*) topInst;
  
  } catch(std::exception& exc) {
    *err = true;
    Error e; 
    e.message(exc.what());
    c->error(e);
  }

  return mod;
}

Instantiable* getSymbol(Context* c, string nsname, string iname) {
  if (c->hasNamespace(nsname)) {
    if (c->getNamespace(nsname)->hasInstantiable(iname)) {
      return c->getNamespace(nsname)->getInstantiable(iname);
    }
  }
  string msg = "Missing Symbol: " + nsname + "." + iname;
  throw std::runtime_error(msg);
  return nullptr;
}

Params json2Params(Context* c, json j) {
  Params g;
  if (j.is_null()) return g;
  for (auto jmap : j.get<jsonmap>()) {
    g[jmap.first] = Str2Param(jmap.second.get<string>());
  }
  return g;
}

Args json2Args(Context* c, Params genparams, json j) {
  Args gargs = Args();
  if (j.is_null()) return gargs;

  //TODO this following code should make sure there are the same number of key-value pairs
  for (auto pmap : genparams) {
    string key = pmap.first;
    Param kind = pmap.second;
    Arg* g;
    switch(kind) {
      case AINT : g = c->int2Arg(j.at(key).get<int>()); break;
      case ASTRING : g = c->string2Arg(j.at(key).get<string>()); break;
      case ATYPE : g = c->type2Arg(json2Type(c,j.at(key))); break;
      default :  throw std::runtime_error(Param2Str(kind) + "is not a type!");
    }
    gargs[key] = g;
  }
  return gargs;
}

Type* json2Type(Context* c, json jt) {
  vector<json> args =jt.get<vector<json>>();
  string kind = args[0].get<string>();
  if (kind == "BitIn") return c->BitIn();
  else if (kind == "BitOut") return c->BitOut();
  else if (kind == "Array") {
    uint n = args[1].get<uint>();
    Type* t = json2Type(c,args[2]);
    return c->Array(n,t);
  }
  else if (kind == "Record") {
    vector<myPair<string,Type*>> rargs;
    for (auto it : args[1].get<vector<vector<json>>>())
      
      rargs.push_back({it[0].get<string>(),json2Type(c,it[1])});
    return c->Record(rargs);
  }
  else {
    cout << "ERROR NYI!: " << args[0].get<string>() << endl;
    assert(false);
  }
  return c->Any();
}

//true cannot open file
void saveModule(Module* m, string filename, bool* err) {
  Context* c = m->getContext();
  std::ofstream file(filename);
  if (!file.is_open()) {
    *err =true;
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
  j["namespaces"]["_G"] = m->getContext()->getGlobal()->toJson();
  file << std::setw(3) << j;
  return;
}



json Args2Json(Args args);
json Params2Json(Params gp);
json Wireable2Json(Wireable* w);

json Type::toJson() { 
  return json::array({TypeKind2Str(kind)});
}
json ArrayType::toJson() {
  return json::array({TypeKind2Str(kind),len,elemType->toJson()});
}
json RecordType::toJson() {
  json jfields;
  for (auto sel : _order) jfields.push_back(json::array({sel,record[sel]->toJson()}));
  return json::array({TypeKind2Str(kind),jfields});
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

json Instantiable::toJson() {
  return {
    {"configparams",Params2Json(configparams)},
    {"metadata",metadata.toJson()}
  };
}

json Module::toJson() {
  json j = Instantiable::toJson();
  j["type"] = type->toJson();
  j["def"] = hasDef() ? getDef()->toJson() : json();
  return j;
}

json Generator::toJson() {
  json j = Instantiable::toJson();
  j["genparams"] = Params2Json(genparams);
  j["typegen"] = "NYI";
  return j;
}

json ModuleDef::toJson() {
  json j;
  j["metadata"] = metadata.toJson();
  j["implementations"] = implementations.toJson();
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
  return json::array({Wireable2Json(first), Wireable2Json(second), metadata.toJson()});
}

json Wireable2Json(Wireable* w) {
  json j;
  json jpath = json::array();
  WirePath path = w->getPath();
  for (auto str : path.second) jpath.push_back(str);
  j["metadata"] = w->getMetadata().toJson();
  j["path"] = json::array({path.first,jpath});
  return j;
}

json Instance::toJson() {
  json j;
  j["instref"] = json::array({instRef->getNamespace()->getName(),instRef->getName()});
  j["genargs"] = this->isGen() ? Args2Json(genargs) : json();
  j["config"] = this->hasConfig() ? Args2Json(this->getConfig()) : json();
  j["metadata"] = metadata.toJson();
  return j;
}

json Metadata::toJson() {
  return json(); // TODO
  json j;
  for (auto it : metadata) j[it.first] = it.second;
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
json ArgType::toJson() { return t->toJson(); }

}//CoreIR namespace

#endif //FILEIO_CPP_
