#include <fstream>
#include "coreir/ir/json.h"
#include "coreir/ir/context.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/types.h"
#include "coreir/ir/typegen.h"
#include "coreir/ir/common.h"
#include "coreir/ir/error.h"
#include "coreir/ir/generator.h"
#include "coreir/ir/module.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/wireable.h"
#include "coreir/ir/value.h"
#include "coreir/ir/dynamic_bit_vector.h"

using namespace std;

namespace CoreIR {

//TODO wrap everything in an empty namespace
using json = nlohmann::json;
typedef map<string,json> jsonmap;
typedef vector<json> jsonvector;

Type* json2Type(Context* c, json jt);
Values json2Values(Context* c, json j, Module* m=nullptr);
ValueType* json2ValueType(Context* c,json j);
Params json2Params(Context* c,json j);

Module* getModSymbol(Context* c, string nsname, string iname);
Module* getModSymbol(Context* c, string ref);
Generator* getGenSymbol(Context* c, string nsname, string iname);

#define ASSERTTHROW(cond,msg) \
  do { \
    if (!(cond)) { \
      throw std::runtime_error(msg); \
    } \
  } while (0)

vector<string> getRef(string s) {
  auto p = splitString<vector<string>>(s,'.');
  ASSERTTHROW(p.size()==2,s + " is not a valid Ref");
  return p;
}

//This will verify that json contains ONLY list of possible things
void checkJson(json j, unordered_set<string> optsRequired, unordered_set<string> optsOptional=unordered_set<string>()) {
  jsonmap jmap = j.get<jsonmap>();
  for (auto req : optsRequired) {
    ASSERTTHROW(jmap.count(req), "Missing " + req + " from\n " + toString(j));
  }

  for (auto opt : jmap) {
    
    ASSERTTHROW(optsRequired.count(opt.first) || optsOptional.count(opt.first),"Cannot put \"" + opt.first + "\" here in json file\n" + toString(j));
  }
}

bool loadFromFile(Context* c, string filename,Module** top) {
  std::fstream file;
  file.open(filename);
  if (!file.is_open()) {
    Error e;
    e.message("Cannot open file " + filename);
    c->error(e);
    return false;
  }
  json j;

  try {
    file >> j;
    //There are the following dependencies moduleDefs->(all modules/generaors)->typegens->(all Types)->namespaces
    //Therefore first load all namespaces
    //Then load all namedtypes (No namedtypegens, only simple named types)
    //Then Load all typegens
    //Then Load all Modules and Generators
    //Then Load all ModuleDefs

    vector<std::pair<Namespace*,json>> nsqueue;
    checkJson(j,{"namespaces"},{"top"});
    for (auto jnsmap : j.at("namespaces").get<jsonmap>() ) {
      string nsname = jnsmap.first;
      checkJson(jnsmap.second,unordered_set<string>(),{"namedtypes","typegens","modules","generators"});
      Namespace* ns;
      if (c->hasNamespace(nsname) ) {
        ns = c->getNamespace(nsname);
      }
      else {
        ns = c->newNamespace(nsname);
      }
      nsqueue.push_back({ns,jnsmap.second});
    }

    //create all namedtypes
    for (auto jnsmap : j.at("namespaces").get<jsonmap>() ) {
      string nsname = jnsmap.first;
      json jns = jnsmap.second;
      Namespace* ns = c->getNamespace(nsname);
      
      //TODO test out weird cases like Named(libA,Named(libB,Named(libA)))
      if (jns.count("namedtypes")) {
        for (auto jntype : jns.at("namedtypes").get<jsonmap>()) {
          checkJson(jntype.second,{"flippedname","rawtype"});
          string name = jntype.first;
          string nameFlip = jntype.second.at("flippedname");
          Type* raw = json2Type(c,jntype.second.at("rawtype"));
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
    }

    //create all typegens
    for (auto jnsmap : j.at("namespaces").get<jsonmap>() ) {
      string nsname = jnsmap.first;
      json jns = jnsmap.second;
      Namespace* ns = c->getNamespace(nsname);
      
      //TODO this is a little sketch because if there is a symbol conflict, I just make sure they are consistent
      //Really, it is possible that I want to concat multiple typegen lists together, ore handle duplicate symbols a different way
      if (jns.count("typegens")) {
        for (auto jtgpair : jns.at("typegens").get<jsonmap>()) {
          string name = jtgpair.first;
          //Get the typegen if it already exists
          TypeGen* tg = ns->hasTypeGen(name) ? ns->getTypeGen(name) : nullptr;

          jsonvector jtg = jtgpair.second.get<jsonvector>();
          Params tgparams = json2Params(c,jtg[0]);
          string tgkind = jtg[1].get<string>();
          if (tgkind == "implicit") {
            ASSERTTHROW(jtg.size()==2,"Bad implicit typegen format" + toString(jtg));
            if (!tg) {
              tg = TypeGenImplicit::make(ns,name,tgparams);
              ns->addTypeGen(tg);
            }
          }
          else if (tgkind == "sparse") {
            vector<std::pair<Values,Type*>> typeList;
            //First just get the list of Values->Types
            for (auto jvaltypes : jtg[2].get<jsonvector>()) {
              jsonvector jvaltype = jvaltypes.get<jsonvector>();
              ASSERTTHROW(jvaltype.size()==2,"Bad sparse typegen format" + toString(jtg[2]));
              Values jvals = json2Values(c,jvaltype[0]);
              Type* t = json2Type(c,jvaltype[1]);
              typeList.push_back({jvals,t});
            }
            if (tg) { //If already exists, just check for consistency
              for (auto vtpair : typeList) {
                ASSERTTHROW(tg->getType(vtpair.first)==vtpair.second,"Typegens are inconsistent... " + tg->toString());
              }
            }
            else {
              tg = TypeGenSparse::make(ns,name,tgparams,typeList);
              ns->addTypeGen(tg);
            }
          }
          else {
            ASSERTTHROW(0,"NYI typegenkind="+tgkind);
          }
        }
      }
    }
    
    //Saves module declaration and the json representing the module
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
            //TODO confirm that is has the same everything like genparams 
            continue;
          }
          
          json jmod = jmodmap.second;
          checkJson(jmod,{"type"},{"modparams","defaultmodargs","instances","connections","metadata"});
          Type* t = json2Type(c,jmod.at("type"));
          Params modparams;
          if (jmod.count("modparams")) {
            modparams = json2Params(c,jmod.at("modparams"));
          }
          Module* m = ns->newModuleDecl(jmodname,t,modparams);
          if (jmod.count("defaultmodargs")) {
            m->addDefaultModArgs(json2Values(c,jmod.at("defaultmodargs")));
          }
          if (jmod.count("metadata")) {
            m->setMetaData(jmod["metadata"]);
          }
          modqueue.push_back({m,jmod});
        }
      }
      if (jns.count("generators")) {
        for (auto jgenmap : jns.at("generators").get<jsonmap>()) {
          string genname = jgenmap.first;
          if (ns->hasGenerator(genname)) {
            //TODO confirm that it has the same everything like genparams and modparams
            continue;
          }

          json jgen = jgenmap.second;
          checkJson(jgen,{"typegen","genparams"},{"modules","defaultgenargs","metadata"});
          Params genparams = json2Params(c,jgen.at("genparams"));
          
          string typeGenName = jgen.at("typegen").get<string>();
          ASSERTTHROW(c->hasTypeGen(typeGenName),"Missing typegen symbol " + typeGenName + " for generator " + jgenmap.first);
          TypeGen* tg = c->getTypeGen(typeGenName);
          vector<std::pair<Values,json>> genmodvalues;
          //Verify that this is consistent with all the types
          //TODO deal with module parameter generation
          Generator* g = ns->newGeneratorDecl(genname,tg,genparams);
          if (jgen.count("defaultgenargs")) {
            g->addDefaultGenArgs(json2Values(c,jgen.at("defaultgenargs")));
          }
          if (jgen.count("metadata")) {
            g->setMetaData(jgen["metadata"]);
          }
          if (jgen.count("modules")) {
            for (auto jgenmod : jgen.at("modules").get<jsonvector>()) {
              jsonvector jvalmod = jgenmod.get<jsonvector>();
              ASSERTTHROW(jvalmod.size()==2,"Bad generated module" + toString(jgenmod));
              Values genargs = json2Values(c,jvalmod[0]);
              json jmod = jvalmod[1];
              checkJson(jmod,{"type"},{"modparams","defaultmodargs","instances","connections","metadata"});
              Type* type = json2Type(c,jmod.at("type"));
              //This will verify the correct type if typegen can generate the type
              Module* m = g->getModule(genargs,type);
              modqueue.push_back({m,jmod}); //Populate the generated module cache
            }
          }
        }
      }
    }
    //Now do all the ModuleDefinitions
    for (auto mq : modqueue) {
      Module* m = mq.first;
      json jmod = mq.second;
      if (!jmod.count("instances") && !jmod.count("connections")) {
        continue;
      }
      ModuleDef* mdef = m->newModuleDef();
      if (jmod.count("instances")) {
        for (auto jinstmap : jmod.at("instances").get<jsonmap>()) {
          string instname = jinstmap.first;
          json jinst = jinstmap.second;
          checkJson(jinst,unordered_set<string>(),{"modref","genref","genargs","modargs","metadata",});
          // This function can throw an error
          Instance* inst;
          if (jinst.count("modref")) {
            assert(jinst.count("genref")==0);
            assert(jinst.count("genargs")==0);
            Module* modRef = getModSymbol(c,jinst.at("modref").get<string>());
            Values modargs;
            if (jinst.count("modargs")) {
              modargs = json2Values(c,jinst.at("modargs"),modRef);
            }
            inst = mdef->addInstance(instname,modRef,modargs);
          }
          else if (jinst.count("genargs") && jinst.count("genref")) { // This is a generator
            auto gref = getRef(jinst.at("genref").get<string>());
            Generator* genRef = getGenSymbol(c,gref[0],gref[1]);
            Values genargs = json2Values(c,jinst.at("genargs"));
            Values modargs;
            if (jinst.count("modargs")) {
              modargs = json2Values(c,jinst.at("modargs"));
            }
            inst = mdef->addInstance(instname,genRef,genargs,modargs);
          }
          else {
            ASSERTTHROW(0,"Bad Instance. Need (modref || (genref && genargs)) " + instname);
          }
          if (jinst.count("metadata")) {
            inst->setMetaData(jinst["metadata"]);
          }
        } // End Instances
      }

      //Connections
      if (jmod.count("connections")) {
        for (auto jcon : jmod.at("connections").get<vector<vector<string>>>()) {
          ASSERTTHROW(jcon.size()==2,"Connection invalid");
          mdef->connect(jcon[0],jcon[1]);
        }
      }
      
      //Add Def back in
      m->setDef(mdef);
    } //End Module loop

    //If top exists return it
    if (top && j.count("top")) {
      *top = getModSymbol(c,j["top"].get<string>());
      c->setTop(*top);
    }
    else if (top) {
      *top = nullptr;
    }
  } catch(std::exception& exc) {
    Error e; 
    e.message("In file: " + filename);
    e.message(exc.what());
    
    c->error(e);
    return false;
  }
  return true;
}

Module* getModSymbol(Context* c, string ref) {
  auto mref = getRef(ref);
  return getModSymbol(c,mref[0],mref[1]);
}

Module* getModSymbol(Context* c, string nsname, string iname) {
  if (c->hasNamespace(nsname)) {
    if (c->getNamespace(nsname)->hasModule(iname)) {
      return c->getNamespace(nsname)->getModule(iname);
    }
  }
  string msg = "Missing Module Symbol: " + nsname + "." + iname;
  throw std::runtime_error(msg);
}

Generator* getGenSymbol(Context* c, string nsname, string iname) {
  if (c->hasNamespace(nsname)) {
    if (c->getNamespace(nsname)->hasGenerator(iname)) {
      return c->getNamespace(nsname)->getGenerator(iname);
    }
  }
  string msg = "Missing Generator Symbol: " + nsname + "." + iname;
  throw std::runtime_error(msg);
}

ValueType* json2ValueType(Context* c,json j) {
  if (j.type() == json::value_t::array) {
    ASSERT(j[0].get<string>()=="BitVector","Bad string for ValueType");
    return c->BitVector(j[1].get<int>());
  }
  string vs = j.get<string>();
  if (vs=="Bool") {
    return c->Bool();
  }
  else if(vs=="Int") {
    return c->Int();
  }
  else if(vs=="String") {
    return c->String();
  }
  else if(vs=="CoreIRType") {
    return CoreIRType::make(c);
  }
  else if(vs=="Module") {
    return ModuleType::make(c);
  }
  else if(vs=="Json") {
    return JsonType::make(c);
  }
  else if(vs=="Any") {
    return AnyType::make(c);
  }
  else {
    ASSERT(0,vs + " is not a ValueType");
  }
}

Params json2Params(Context* c,json j) {
  Params g;
  if (j.is_null()) return g;
  for (auto jmap : j.get<jsonmap>()) {
    g[jmap.first] = json2ValueType(c,jmap.second);
  }
  return g;
}

Value* json2Value(Context* c, json j,Module* m) {
  auto jlist = j.get<jsonvector>();
  ValueType* vtype = json2ValueType(c,jlist[0]);
  if (jlist.size()==3) {
    //Arg
    ASSERT(jlist[1].get<string>()=="Arg","Value with json array of size=3 must be an Arg");
    ASSERT(m,"Can only use 'Arg' reference in modargs");
    return m->getArg(jlist[2].get<string>());
  }
  json jval = jlist[1];
  ASSERT(jlist.size()==2,"NYI");
  switch(vtype->getKind()) {
    case ValueType::VTK_Bool : return Const::make(c,jval.get<bool>());
    case ValueType::VTK_Int : return Const::make(c,jval.get<int>());
    case ValueType::VTK_BitVector : {
      ASSERTTHROW(jval.is_string(),toString(jval) + " needs to be a bitvector string <N>'h<value>");
      auto bv = BitVector(jval.get<string>());
      assert(bv.bitLength() == cast<BitVectorType>(vtype)->getWidth());
      return Const::make(c,bv);                                 
    }
    case ValueType::VTK_String : return Const::make(c,jval.get<string>());
    case ValueType::VTK_CoreIRType : return Const::make(c,json2Type(c,jval));
    case ValueType::VTK_Module : {
      Module* mod;
      if (jval.type() == json::value_t::array) { //This is a generated module
        vector<json> jgenmod = jval.get<vector<json>>();
        ASSERTTHROW(jgenmod.size()==2,"Badly constructed module");
        mod = c->getGenerator(jgenmod[0].get<string>())->getModule(json2Values(c,jgenmod[1],m));
      }
      else {
        mod = c->getModule(jval.get<string>());
      }
      return Const::make(c,mod);
    }
    case ValueType::VTK_Json : return Const::make(c,jval);
    default : ASSERT(0,"Cannot have a Const of type" + vtype->toString());
  }
}

Values json2Values(Context* c, json j,Module* m) {
  Values values; 

  for (auto jmap : j.get<jsonmap>()) {
    string key = jmap.first;
    values[jmap.first] = json2Value(c,jmap.second,m);
  }
  return values;
}


Type* json2Type(Context* c, json jt) {
  if (jt.type() == json::value_t::string) {
    //Will be bitIn or Bit
    string kind = jt.get<string>();
    if (kind == "BitIn") {
      return c->BitIn();
      
    } else if (kind == "Bit") {
      return c->Bit();
    } else if (kind == "BitInOut") {
      return c->BitInOut();
    } else {
      throw std::runtime_error(kind + " is not a type!");
    }
  }
  else if (jt.type() == json::value_t::array) {
    jsonvector args = jt.get<jsonvector>();
    string kind = args[0].get<string>();
    if (kind == "Array") {
      uint n = args[1].get<uint>();
      Type* t = json2Type(c,args[2]);
      return c->Array(n,t);
    }
    else if (kind == "Record") {
      RecordParams rparams;
      for (auto it : args[1].get<jsonvector>()) {
        jsonvector field = it.get<jsonvector>();
        ASSERT(field.size()==2, "Invalid Record field" + toString(it));
        rparams.push_back({field[0].get<string>(),json2Type(c,field[1])});
      }
      return c->Record(rparams);
    }
    else if (kind == "Named") {
      ASSERTTHROW(args.size()==2,"Invalid Named Type field" + toString(jt));
      vector<string> info = getRef(args[1].get<string>());
      std::string nsname = info[0];
      std::string name   = info[1];
      return c->Named(nsname+"."+name);
    }
    else {
      cout << "ERROR NYI!: " << args[0].get<string>() << endl;
      assert(false);
      return NULL;
    }
  }
  else throw std::runtime_error("Error parsing Type");
}

#undef ASSERTTHROW

}//CoreIR namespace
