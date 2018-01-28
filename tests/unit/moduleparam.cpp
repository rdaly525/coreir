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
        {"in",c->BitIn()->Arr(width)->Arr(2)->Arr(N)},
        {"out",c->Bit()->Arr(width)->Arr(N)}
      });
    }
  );


  Generator* map = g->newGeneratorDecl("map",g->getTypeGen("map_type"),{{"N",c->Int()},{"op",ModuleType::make(c)}});
  map->setGeneratorDefFromFun([](Context* c, Values args, ModuleDef* def) {
    Module* op = args.at("op")->get<Module*>();
    uint N = args.at("N")->get<int>();
    for (uint i=0; i<N; ++i) {
      Instance* opN = def->addInstance("op"+to_string(i),op);
      def->connect(opN->sel("in0"),def->getInterface()->sel("in")->sel(i)->sel(0));
      def->connect(opN->sel("in1"),def->getInterface()->sel("in")->sel(i)->sel(1));
      def->connect(opN->sel("out"),def->getInterface()->sel("out")->sel(i));
    }
  });
  Module* test = c->getGlobal()->newModuleDecl("testModule",c->Record());
  ModuleDef* def = test->newModuleDef();
  Module* mul = c->getGenerator("coreir.mul")->getModule({{"width",Const::make(c,13)}});
  
  Instance* map_mul = def->addInstance("map_mul", "global.map", {{"N",Const::make(c,5)},{"op",Const::make(c,mul)}});
  test->setDef(def);
  test->print();
  map_mul->getModuleRef()->print();
  c->runPasses({"rungenerators"});
  test->print();
  map_mul->getModuleRef()->print();
  deleteContext(c);
  return 0;
}
