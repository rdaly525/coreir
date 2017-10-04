#include <fstream>
#include "coreir/ir/json.h"
#include "coreir/ir/context.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/types.h"
#include "coreir/ir/typegen.h"
#include "coreir/ir/common.h"
#include "coreir/ir/error.h"
#include "coreir/ir/instantiable.h"
#include "coreir/ir/moduledef.h"
#include "coreir/ir/wireable.h"
#include "coreir/ir/value.h"
#include "coreir/ir/dynamic_bit_vector.h"

using namespace std;

namespace CoreIR {

using json = nlohmann::json;
typedef map<string,json> jsonmap;


Type* json2Type(Context* c, json jt);
Values json2Values(Context* c, json j);
ValuePtr json2Value(Context* c, json j);
ValueType* json2ValueType(Context* c,json j);
Params json2Params(Context* c,json j);

Module* getModSymbol(Context* c, string nsname, string iname);
Module* getModSymbol(Context* c, string ref);
Generator* getGenSymbol(Context* c, string nsname, string iname);

#define ASSERTTHROW(cond,msg) \
  if (!(cond)) throw std::runtime_error(msg)

vector<string> getRef(string s) {
  auto p = splitString<vector<string>>(s,'.');
  ASSERTTHROW(p.size()==2,s + " is not a valid Ref");
  return p;
}

//This will verify that json contains ONLY list of possible things
void checkJson(json j, unordered_set<string> opts) {
  for (auto opt : j.get<jsonmap>()) {
    ASSERTTHROW(opts.count(opt.first),"Cannot put \"" + opt.first + "\" here in json file");
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
    //There are the following dependencies moduleDefs->(all modules)->(all types)
    //Therefore first load all namedtypes and typegens
    //Then Load all Modules and Generators
    //Then Load all ModuleDefs

    vector<std::pair<Namespace*,json>> nsqueue;

    checkJson(j,{"top","namespaces"});
    //Get or create namespace
    for (auto jnsmap : j.at("namespaces").get<jsonmap>() ) {
      string nsname = jnsmap.first;
      json jns = jnsmap.second;
      checkJson(jns,{"namedtypes","namedtypegens","modules","generators"});
      Namespace* ns;
      if (c->hasNamespace(nsname) ) ns = c->getNamespace(nsname);
      else ns = c->newNamespace(nsname);
      
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
      //For namedtypegens I cannot really construct these without the typegenfunction. Therefore I will just verify that they exist
      if (jns.count("namedtypegens")) {
        for (auto jntypegen : jns.at("namedtypegens").get<jsonmap>()) {
          checkJson(jntypegen.second,{"genparams","flippedname"});
          string name = jntypegen.first;
          Params genparams = json2Params(c,jntypegen.second.at("genparams"));
          if (!ns->hasTypeGen(name)) {
            throw std::runtime_error("Missing namedtypegen symbol: " + ns->getName() + "." + name);
          }
            
          TypeGen* typegen = ns->getTypeGen(name);
          assert(typegen->getParams() == genparams);
          assert(!typegen->isFlipped());
          if (jntypegen.second.count("flippedname")) {
            string nameFlip = jntypegen.second.at("flippedname");
            typegen = ns->getTypeGen(nameFlip);
            assert(typegen->getParams() == genparams);
            assert(typegen->isFlipped());
          }
        }
      }
      nsqueue.push_back({ns,jns});
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
          checkJson(jmod,{"type","modparams","defaultmodargs","instances","connections"});
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
          string jgenname = jgenmap.first;
          //TODO for now, if it has a module already, just skip
          if (ns->hasGenerator(jgenname)) {
            //TODO confirm that it has the same everything like genparams and modparams
            continue;
          }

          json jgen = jgenmap.second;
          checkJson(jgen,{"typegen","genparams","defaultgenargs"});
          Params genparams = json2Params(c,jgen.at("genparams"));
          auto tgenref = getRef(jgen.at("typegen").get<string>());
          TypeGen* typegen = c->getTypeGen(jgen.at("typegen").get<string>());
          assert(genparams == typegen->getParams());
          Params modparams;
          Generator* g = ns->newGeneratorDecl(jgenname,typegen,genparams);
          //if (jgen.count("defaultmodargs")) {
          //  g->addDefaultModArgs(json2Values(c,modparams,jgen.at("defaultmodargs")));
          //}
          if (jgen.count("defaultgenargs")) {
            g->addDefaultGenArgs(json2Values(c,jgen.at("defaultgenargs")));
          }
          if (jgen.count("metadata")) {
            g->setMetaData(jgen["metadata"]);
          }
        }
      }
    }
    //Now do all the ModuleDefinitions
    for (auto mq : modqueue) {
      Module* m = mq.first;
      json jmod = mq.second;
      if (!jmod.count("instances") && !jmod.count("connections")) continue;
      
      ModuleDef* mdef = m->newModuleDef();
      if (jmod.count("instances")) {
        for (auto jinstmap : jmod.at("instances").get<jsonmap>()) {
          string instname = jinstmap.first;
          json jinst = jinstmap.second;
          checkJson(jinst,{"modref","genref","genargs","modargs"});
          // This function can throw an error
          if (jinst.count("modref")) {
            assert(jinst.count("genref")==0);
            assert(jinst.count("genargs")==0);
            Module* modRef = getModSymbol(c,jinst.at("modref").get<string>());
            Values modargs;
            if (jinst.count("modargs")) {
              modargs = json2Values(c,jinst.at("modargs"));
            }
            mdef->addInstance(instname,modRef,modargs);
          }
          else if (jinst.count("genargs") && jinst.count("genref")) { // This is a generator
            auto gref = getRef(jinst.at("genref").get<string>());
            Generator* genRef = getGenSymbol(c,gref[0],gref[1]);
            Values genargs = json2Values(c,jinst.at("genargs"));
            Values modargs;
            if (jinst.count("modargs")) {
              modargs = json2Values(c,jinst.at("modargs"));
            }
            mdef->addInstance(instname,genRef,genargs,modargs);
          }
          else {
            ASSERTTHROW(0,"Bad Instance. Need (modref || (genref && genargs))");
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
    return c->CoreIRType();
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

ValuePtr json2Value(Context* c, json j) {
  auto jlist = j.get<vector<json>>();
  string vkind = jlist[0].get<string>();
  ValueType* vtype = json2ValueType(c,jlist[1]);
  json jval = jlist[2];
  if (vkind=="Arg") {
    return Arg::make(vtype,jlist[2].get<string>());
  }
  ASSERT(vkind=="Const","NYI " + vkind);
  switch(vtype->getKind()) {
    case Value::VK_ConstBool : return ConstBool::make(vtype,jval.get<bool>());
    case Value::VK_ConstInt : return ConstInt::make(vtype,jval.get<int>());
    case Value::VK_ConstBitVector : return ConstBitVector::make(vtype,BitVector(cast<BitVectorType>(vtype)->getWidth(),jval.get<string>()));
    case Value::VK_ConstString : return ConstString::make(vtype,jval.get<string>());
    case Value::VK_ConstCoreIRType : return ConstCoreIRType::make(vtype,json2Type(c,jval));
    default : ASSERT(0,"Cannot have a Const of type" + vtype->toString());
  }
}

Values json2Values(Context* c, json j) {
  Values values; 

  for (auto jmap : j.get<jsonmap>()) {
    string key = jmap.first;
    values[jmap.first] = json2Value(c,jmap.second);
  }
  return values;
}


Type* json2Type(Context* c, json jt) {
  if (jt.type() == json::value_t::string) {
    //Will be bitIn or Bit
    string kind = jt.get<string>();
    if (kind == "BitIn") return c->BitIn();
    else if (kind == "Bit") return c->Bit();
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
      RecordParams rparams;
      for (auto it : args[1].get<jsonmap>()) {
        rparams.push_back({it.first,json2Type(c,it.second)});
      }
      return c->Record(rparams);
    }
    else if (kind == "Named") {
      vector<string> info = getRef(args[1].get<string>());
      std::string nsname = info[0];
      std::string name   = info[1];
      if (args.size()==3) { //Has args
        Params genparams = c->getNamespace(nsname)->getTypeGen(name)->getParams();
        Values genargs = json2Values(c,args[2]);
        return c->Named(nsname+"."+name,genargs);
      }
      return c->Named(nsname+"."+name);
    }
    else {
      cout << "ERROR NYI!: " << args[0].get<string>() << endl;
      assert(false);
    }
  }
  else throw std::runtime_error("Error parsing Type");
}

#undef ASSERTTHROW

}//CoreIR namespace
