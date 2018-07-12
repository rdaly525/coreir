#include "coreir.h"
#include <cassert>

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  Json jdata;
  jdata["mylist"][0] = 5;
  jdata["mylist"][1] = "string";
  jdata["mylist"][2] = {{"a",13},{"b",2}};
  Values g5 = {{"a",Const::make(c,jdata)}};
  checkValuesAreParams(g5,{{"a",JsonType::make(c)}});
  cout << "jsonval: " << jdata << endl;
  cout << "jsonval2: " << g5.at("a")->get<Json>() << endl;
  
  
  Namespace* g = c->getGlobal();
  
  //Declare a TypeGenerator (in global) for addN
  g->newTypeGen(
    "json_type", //name for the typegen
    {{"width",c->Any()}},
    [](Context* c, Values args) { //Function to compute type
      Json width = args.at("width")->get<Json>();
      return c->Record({
        {"in",c->BitIn()->Arr(width["mylist"][0])->Arr(width.at("mylist")[2].at("a"))},
        {"out",c->Bit()->Arr(3)}
      });
    }
  );


  g->newGeneratorDecl("addN",g->getTypeGen("json_type"),{{"width",c->Any()}});
  
  Module* top = g->newModuleDecl("top",c->Record());
  ModuleDef* def = top->newModuleDef();
  def->addInstance("inst","global.addN",{{"width",Const::make(c,jdata)}});
  top->setDef(def);
  top->print();
  
  if (!saveToFile(g, "_anytest.json",top)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }

  deleteContext(c);
  
  c = newContext();
  cout << "loading" << endl;
  if (!loadFromFile(c,"_anytest.json")) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  ASSERT(jdata == c->getModule("global.top")->getDef()->getInstances().at("inst")->getModuleRef()->getGenArgs().at("width")->get<Json>(),"jdata is not the same!");
  deleteContext(c);

  return 0;
}
