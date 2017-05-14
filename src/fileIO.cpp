#include "json.hpp"
#include <iostream>
#include <fstream>
#include "context.hpp"
#include "instantiable.hpp"
#include "namespace.hpp"
#include "typegen.hpp"
#include <unordered_map>


namespace CoreIR {

typedef unordered_map<string,json> jsonmap;

using json = nlohmann::json;

Type* json2Type(Context* c, json jt);
Args json2Args(Context* c, Params p, json j);
Params json2Params(json j);

Module* getModSymbol(Context* c, string nsname, string iname);
Generator* getGenSymbol(Context* c, string nsname, string iname);

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

  try {
    string topnsname = j.at("top").at(0);
    string topmodname = j.at("top").at(1);
    
    //There are the following dependencies moduleDefs->(all modules)->(all types)
    //Therefore first load all namedtypes and typegens
    //Then Load all Modules and Generators
    //Then Load all ModuleDefs

    vector<std::pair<Namespace*,json>> nsqueue;

    //Get or create namespace
    for (auto jnsmap : j.at("namespaces").get<jsonmap>() ) {
      string nsname = jnsmap.first;
      json jns = jnsmap.second;
      Namespace* ns;
      if (c->hasNamespace(nsname) ) ns = c->getNamespace(nsname);
      else ns = c->newNamespace(nsname);
      
      //TODO test out weird cases like Named(libA,Named(libB,Named(libA)))
      if (jns.count("namedtypes")) {
        for (auto jntype : jns.at("namedtypes").get<vector<json>>()) {
          string name = jntype.at("name");
          string nameFlip = jntype.at("flippedname");
          Type* raw = json2Type(c,jntype.at("rawtype"));
          if (ns->hasNamedType(name)) {
            //Verify it also has nameflip
            NamedType* namedtype = ns->getNamedType(name);
            assert(raw==namedtype->getRaw());
            assert(c->Flip(namedtype) == ns->getNamedType(nameFlip));
          }
          else {
            ns->newNamedType(name,nameFlip,raw);
          }
        }
      }
      //For namedtypegens I cannot really construct these without the typegenfunction. Therefore I will just verify that they exist
      if (jns.count("namedtypegens")) {
        for (auto jntypegen : jns.at("namedtypegens").get<vector<json>>()) {
          string name = jntypegen.at("name");
          Params genparams = json2Params(jntypegen.at("genparams"));
          if (!ns->hasTypeGen(name)) {
            throw std::runtime_error("Missing namedtypegen symbol: " + ns->getName() + "." + name);
          }
            
          TypeGen* typegen = ns->getTypeGen(name);
          assert(typegen->getParams() == genparams);
          assert(!typegen->isFlipped());
          if (jntypegen.count("flippedname")) {
            string nameFlip = jntypegen.at("flippedname");
            typegen = ns->getTypeGen(nameFlip);
            assert(typegen->getParams() == genparams);
            assert(typegen->isFlipped());
          }
        }
      }
      nsqueue.push_back({ns,jns});
    }
    vector<std::pair<Module*,json>> modqueue;
    for (auto nsq : nsqueue) {
      Namespace* ns = nsq.first;
      json jns = nsq.second;
      //Load Modules
      if (jns.count("modules")) {
        for (auto jmodmap : jns.at("modules").get<jsonmap>()) {
          //Figure out type;
          string jmodname = jmodmap.first;
          //TODO for now if it already exists, just skip
          if (ns->hasModule(jmodname)) {
            continue;
          }
          
          json jmod = jmodmap.second;
          Type* t = json2Type(c,jmod.at("type"));
          
          Params configparams;
          if (jmod.count("configparams")) {
            configparams = json2Params(jmod.at("configparams"));
          }
          Module* m = ns->newModuleDecl(jmodname,t,configparams);
          modqueue.push_back({m,jmod});
        }
      }
      if (jns.count("generators")) {
        for (auto jgenmap : jns.at("generators").get<jsonmap>()) {
          string jgenname = jgenmap.first;
          //TODO for now, if it has a module already, just skip
          if (ns->hasGenerator(jgenname)) {
            continue;
          }

          json jgen = jgenmap.second;
          Params genparams = json2Params(jgen.at("genparams"));
          vector<string> tgenref = jgen.at("typegen").get<vector<string>>();
          TypeGen* typegen = c->getTypeGen(tgenref[0],tgenref[1]);
          assert(genparams == typegen->getParams());
          ns->newGeneratorDecl(jgenname,typegen,genparams);
        }
      }
    }

    //Now do all the ModuleDefinitions
    for (auto mq : modqueue) {
      Module* m = mq.first;
      json jmod = mq.second;
      if (!jmod.count("def")) continue;
      
      json jdef = jmod.at("def");
      ModuleDef* mdef = m->newModuleDef();
      if (jdef.count("instances")) {
        for (auto jinstmap : jdef.at("instances").get<jsonmap>()) {
          string instname = jinstmap.first;
          json jinst = jinstmap.second;
          
          // This function can throw an error
          
          if (jinst.count("moduleref")) {
            assert(jinst.count("generatorref")==0);
            assert(jinst.count("genargs")==0);
            json jmodRef = jinst.at("moduleref");
            Module* modRef = getModSymbol(c,jmodRef.at(0),jmodRef.at(1));
            Args configargs;
            if (jinst.count("configargs")) {
              configargs = json2Args(c,modRef->getConfigParams(),jinst.at("configargs"));
            }
            mdef->addInstance(instname,modRef,configargs);
          }
          else if (jinst.count("genargs") && jinst.count("generatorref")) { // This is a generator
            json jgenRef = jinst.at("generatorref");
            Generator* genRef = getGenSymbol(c,jgenRef.at(0),jgenRef.at(1));
            Args genargs = json2Args(c,genRef->getGenparams(),jinst.at("genargs"));
            Args configargs;
            if (jinst.count("configargs")) {
              configargs = json2Args(c,genRef->getConfigParams(),jinst.at("configargs"));
            }
            mdef->addInstance(instname,genRef,genargs,configargs);
          }
          else {
            assert(0);
          }
        } // End Instances
      }

      //Connections
      if (jdef.count("connections")) {
        for (auto jcon : jdef.at("connections").get<vector<vector<json>>>()) {
          vector<string> pathA = jcon[0].get<vector<string>>();
          vector<string> pathB = jcon[1].get<vector<string>>();
          mdef->connect(pathA,pathB);
        }
      }
      
      //Add Def back in
      m->setDef(mdef);
    } //End Module loop
    
    //Reference Top
    mod = getModSymbol(c,topnsname,topmodname);
  
  } catch(std::exception& exc) {
    *err = true;
    Error e; 
    e.message(exc.what());
    c->error(e);
  }

  return mod;
}

Module* getModSymbol(Context* c, string nsname, string iname) {
  if (c->hasNamespace(nsname)) {
    if (c->getNamespace(nsname)->hasModule(iname)) {
      return c->getNamespace(nsname)->getModule(iname);
    }
  }
  string msg = "Missing Symbol: " + nsname + "." + iname;
  throw std::runtime_error(msg);
}

Generator* getGenSymbol(Context* c, string nsname, string iname) {
  if (c->hasNamespace(nsname)) {
    if (c->getNamespace(nsname)->hasGenerator(iname)) {
      return c->getNamespace(nsname)->getGenerator(iname);
    }
  }
  string msg = "Missing Symbol: " + nsname + "." + iname;
  throw std::runtime_error(msg);
}

Params json2Params(json j) {
  Params g;
  if (j.is_null()) return g;
  for (auto jmap : j.get<jsonmap>()) {
    g[jmap.first] = Str2Param(jmap.second.get<string>());
  }
  return g;
}

Args json2Args(Context* c, Params genparams, json j) {
  Args gargs; 

  //TODO this following code should make sure there are the same number of key-value pairs
  for (auto pmap : genparams) {
    string key = pmap.first;
    Param kind = pmap.second;
    Arg* g;
    switch(kind) {
      case AINT : g = c->argInt(j.at(key).get<int>()); break;
      case ASTRING : g = c->argString(j.at(key).get<string>()); break;
      case ATYPE : g = c->argType(json2Type(c,j.at(key))); break;
      default :  throw std::runtime_error(Param2Str(kind) + "is not a valid arg param!");
    }
    gargs[key] = g;
  }
  return gargs;
}

Type* json2Type(Context* c, json jt) {
  if (jt.type() == json::value_t::string) {
    //Will be bitIn or Bit
    string kind = jt.get<string>();
    if (kind == "BitIn") return c->BitIn();
    else if (kind == "Bit") return c->Bit();
    else if (kind == "Any") return c->Any();
    else throw std::runtime_error(kind + " is not a type!");
  }
  else if (jt.type() == json::value_t::array) {
    vector<json> args = jt.get<vector<json>>();
    string kind = args[0].get<string>();
    if (kind == "Array") {
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
    else if (kind == "Named") {
      string nsname = args[1].get<string>();
      string name = args[2].get<string>();
      if (args.size()==4) { //Has args
        Params genparams = c->getNamespace(nsname)->getTypeGen(name)->getParams();
        Args genargs = json2Args(c,genparams,args[3]);
        return c->Named(nsname,name,genargs);
      }
      return c->Named(nsname,name);
    }
    else {
      cout << "ERROR NYI!: " << args[0].get<string>() << endl;
      assert(false);
    }
  }
  else throw std::runtime_error("Error parsing Type");
  return c->Any();
}


//true cannot open file
void saveModule(Module* m, string filename, bool* err) {
  Context* c = m->getContext();
  ASSERT(m->getNamespace() == c->getGlobal(),"Only supports global for now");
  std::ofstream file(filename);
  if (!file.is_open()) {
    *err =true;
    Error e;
    e.message("Cannot open file " + filename);
    e.fatal();
    c->error(e);
    return;
  }

  json j;
  j["top"] = json::array({m->getNamespace()->getName(),m->getName()});
  
  //Only do the global for now
  j["namespaces"][m->getNamespace()->getName()] = m->getNamespace()->toJson();
  file << std::setw(2) << j;
  return;
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
  for (auto sel : _order) jfields.push_back(json::array({sel,record[sel]->toJson()}));
  return json::array({TypeKind2Str(kind),jfields});
}

json NamedType::toJson() {
  json j;
  j.push_back("Named");
  //j.push_back(json::array({ns->getName(),name}));
  j.push_back(ns->getName());
  j.push_back(name);
  j.push_back(Args2Json(genargs));
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
        {"name",n},
        {"flippedname",nFlip},
        {"rawtype", raw->toJson()}
      };
      jntypes.push_back(jntype);
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
        {"name",n},
        {"genparams", Params2Json(tg->getParams())}
      };
      if (nFlip != "") {
        jntypegen["flippedname"] = nFlip;
      }
      jntypegens.push_back(jntypegen);
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
  if (!metadata.empty()) {
    j["metadata"] = metadata.toJson();
  }
  return j;
}

json Module::toJson() {
  json j = Instantiable::toJson();
  j["type"] = type->toJson();
  if (this->hasDef()) {
    j["def"] = this->getDef()->toJson();
  }
  return j;
}

json Generator::toJson() {
  json j = Instantiable::toJson();
  j["genparams"] = Params2Json(genparams);
  //You need to add namespace back to typegen (ugh)
  j["typegen"] = json::array({typegen->getNamespace()->getName(),typegen->getName()});
  return j;
}

json Connection2Json(Connection con) {
  return json::array({Wireable2Json(con.first), Wireable2Json(con.second)});
}

json ModuleDef::toJson() {
  json j;
  if (!metadata.empty()) {
    j["metadata"] = metadata.toJson();
  }
  if (!implementations.empty()) {
    j["implementations"] = implementations.toJson();
  }
  if (!instances.empty()) {
    json jinsts;
    for ( auto instmap : instances) {
      jinsts[instmap.first] = instmap.second->toJson();
    }
    j["instances"] = jinsts;
  }
  if (!connections.empty()) {
    json jcons;
    for (auto con : connections) {
      jcons.push_back(Connection2Json(con));
    }
    j["connections"] = jcons;
  }
  return j;
}

json Wireable2Json(Wireable* w) {
  json j;
  SelectPath path = w->getSelectPath();
  for (auto str : path) j.push_back(str);
  return j;
}

json Instance::toJson() {
  json j;
  if (this->isGen()) {
    j["genargs"] = Args2Json(genargs);
    j["generatorref"] = json::array({generatorRef->getNamespace()->getName(),generatorRef->getName()});
  }
  else {
    j["moduleref"] = json::array({moduleRef->getNamespace()->getName(),moduleRef->getName()});
  }
  if (this->hasConfigArgs()) {
    j["config"] = Args2Json(this->getConfigArgs());
  }
  if (!metadata.empty()) {
    j["metadata"] = metadata.toJson();
  }
  return j;
}

json Metadata::toJson() {
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
