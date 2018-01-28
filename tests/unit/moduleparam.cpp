#include "coreir.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();
  Namespace* g = c->getGlobal();
  //Declare a TypeGenerator (in global) for addN
  g->newTypeGen(
    "map_type", //name for the typegen
    {{"N",c->Int()},
    {"op",ModuleType::make(c)}}, //generater parameters
    [](Context* c, Values args) { //Function to compute type
      Module* op = args.at("op")->get<Module*>();
      assert(op->isGenerated());
      uint width = op->getGenArgs().at("width")->get<int>();
      uint N = args.at("N")->get<int>();
      return c->Record({
        {"in",c->BitIn()->Arr(width)->Arr(N)},
        {"out",c->Bit()->Arr(width)}
      });
    }
  );


  Generator* map = g->newGeneratorDecl("map",g->getTypeGen("map_type"),{{"N",c->Int()},{"op",ModuleType::make(c)}});
  (void) map;
  Module* test = c->getGlobal()->newModuleDecl("testModule",c->Record());
  ModuleDef* def = test->newModuleDef();
  Module* mul = c->getGenerator("coreir.mul")->getModule({{"width",Const::make(c,13)}});
  
  def->addInstance("map_mul", "global.map", {{"N",Const::make(c,5)},{"op",Const::make(c,mul)}});
  test->setDef(def);
  test->print();
  deleteContext(c);
  return 0;
}
