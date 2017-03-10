#include "json.hpp"
#include <iostream>
#include <fstream>
#include "context.hpp"

using json = nlohmann::json;

json Type2Json(Type* t);
json ModuleDef2Json(ModuleDef* md);
json Module2Json(Module* m);
json Wireable2Json(Wireable* w);
json Instance2Json(Instance* i);



Module* loadModule(Context* c, string filename) {
  std::ifstream file(filename);
  json j;
  file >> j;
  cout << "Loading " << filename << endl;
  return nullptr;
}

//False cannot open file
bool saveModule(Module* m, string filename) {
  std::ofstream file(filename);
  if (!file.is_open()) {
    return true;
  }
  json j;
  j["top"] = m->getName();
  j["module"] = Module2Json(m);
 
  file << std::setw(3) << j;
  return false;
}


json Type2Json(Type* t) {
  json j;
  switch(t->getKind()) {
    case(BITIN) : j["BitIn"]; break;
    case(BITOUT) : j["BitOut"]; break;
    case(ARRAY) : {
      ArrayType* at = (ArrayType*) t;
      j["Array"] = json::array({at->getLen(), Type2Json(at->getElemType())});
      break;
    }
    case(RECORD) : j["Record"] = "NYI";
    default : j["TYPE_NYI"];
  }
  return j;
}

json Module2Json(Module* m) {
  m->print();
  json j = {
    {"type",Type2Json(m->getType())},
    {"config","NYI"},
    {"metadata","NYI"},
    {"def",ModuleDef2Json(m->getDef())}
  };
  return j;
}

json ModuleDef2Json(ModuleDef* md) {
  if (!md) return "null";
  json j;
  j["metadata"] = "NYI";
  j["implementations"] = "NYI";
  json jinsts;
  for ( auto inst : md->getInstances()) {
    jinsts.push_back(Instance2Json(inst.second));
  }
  j["instances"] = jinsts;
  json jwires;
  for (auto wire : md->getWires() ) {
    jwires.push_back(json::array({Wireable2Json(wire.first), Wireable2Json(wire.second), {"metadata","NYI"}}));
  }
  j["connections"] = jwires;
  return j;
}

json Wireable2Json(Wireable* w) {
  json j;
  std::pair<string,vector<string>> path = w->getPath();
  j.push_back(path.first);
  for (auto str : path.second) j.push_back(str);
  return j;
}

json Instance2Json(Instance* i) {
  json j;
  Instantiable* iRef = i->getInstRef();
  j["instancename"] = i->getInstname();
  j["instref"] = json::array({iRef->isKind(MOD) ? "module" : "generator",iRef->getNamespace()->getName(),iRef->getName()});
  j["args"] = "NYI";
  j["metadata"] = "NYI";
  return j;
}

/*  
  uint n = 32;
  cout << "Loading from file: " << filename << endl;
  
  Namespace* stdlib = getStdlib(c);
  c->registerLib(stdlib);

  //Declare add2 Generator
  Generator* add2 = stdlib->getGenerator("add2");
  assert(add2);
  // Define Add4 Module
  Type* add4Type = c->Record({
      {"in",c->Array(4,c->Array(n,c->BitIn()))},
      {"out",c->Array(n,c->BitOut())}
  });
  Module* add4_n = c->newModuleDecl("Add4",add4Type);
  ModuleDef* def = add4_n->newModuleDef();
    Wireable* iface = def->getInterface();
    Wireable* add_00 = def->addInstanceGenerator("add00",add2,c->newGenArgs({{"w",c->GInt(n)}}));
    Wireable* add_01 = def->addInstanceGenerator("add01",add2,c->newGenArgs({{"w",c->GInt(n)}}));
    Wireable* add_1 = def->addInstanceGenerator("add1",add2,c->newGenArgs({{"w",c->GInt(n)}}));
    
    def->wire(iface->sel("in")->sel(0),add_00->sel("in0"));
    //def->wire(iface->sel("in")->sel(1)->sel(3),add_00->sel("in0")->sel(3));
    def->wire(iface->sel("in")->sel(1),add_00->sel("in1"));
    def->wire(iface->sel("in")->sel(2),add_01->sel("in0"));
    def->wire(iface->sel("in")->sel(3),add_01->sel("in1"));

    def->wire(add_00->sel("out"),add_1->sel("in0"));
    def->wire(add_01->sel("out"),add_1->sel("in1"));

    def->wire(add_1->sel("out"),iface->sel("out"));
  add4_n->addDef(def);
  c->checkerrors();
  
  // Link v1 of library
  cout << "Linking stdlib!" << endl;
  Namespace* stdlib_v1 = getStdlib_v1(c);
  c->linkLib(stdlib_v1, stdlib);
 
  cout << "Checkign Errors 2" << endl;
  c->checkerrors();
  
  rungenerators(c,add4_n);
  
  add4_n->print();
  
  return add4_n;
}
*/
