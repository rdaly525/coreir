#include "coreir.h"

using namespace std;
using namespace CoreIR;


void checker(Module* m) {
  ModuleDef* def = m->getDef();
  Wireable* w = def->sel("i0");
  cout << w->toString() << endl;
  Instance* i0 = cast<Instance>(def->sel("i0"));
  cout << i0->toString() << endl;
  Module* m0 = i0->getModuleRef();
  assert(m0->getGenArgs().count("ga") && m0->getGenArgs().at("ga")->get<int>()==6);
  assert(m0->getGenArgs().count("gb") && m0->getGenArgs().at("gb")->get<int>()==7);
  assert(i0->getModArgs().count("ca") && i0->getModArgs().at("ca")->get<int>()==11);
  assert(i0->getModArgs().count("cb") && i0->getModArgs().at("cb")->get<int>()==12);
  
  Instance* i1 = cast<Instance>(def->sel("i1"));
  Module* m1 = i1->getModuleRef();
  assert(m1->getGenArgs().count("ga") && m1->getGenArgs().at("ga")->get<int>()==5);
  assert(m1->getGenArgs().count("gb") && m1->getGenArgs().at("gb")->get<int>()==7);
  assert(i1->getModArgs().count("ca") && i1->getModArgs().at("ca")->get<int>()==10);
  assert(i1->getModArgs().count("cb") && i1->getModArgs().at("cb")->get<int>()==12);
}

int main() {
  
  // New context
  Context* c = newContext();
  
  //create generator with some defaults
  Namespace* g = c->getGlobal();
  
  //Declare a TypeGenerator (in global) for addN
  g->newTypeGen(
    "default_type", //name for the typegen
    {{"ga",c->Int()},{"gb",c->Int()}}, //generater parameters
    [](Context* c, Values args) { //Function to compute type
      return c->Record();
    }
  );


  Generator* d = g->newGeneratorDecl("defaults",g->getTypeGen("default_type"),{{"ga",c->Int()},{"gb",c->Int()}});
  d->setModParamsGen([](Context* c, Values genargs) -> std::pair<Params,Values> {
    Params p({{"ca",c->Int()},{"cb",c->Int()}});
    Values d({{"ca",Const::make(c,10)}});
    return {p,d};
  });
  //Set defaults for ga and ca
  d->addDefaultGenArgs({{"ga",Const::make(c,5)}});

  Module* tester = g->newModuleDecl("Tester",c->Record());
  ModuleDef* def = tester->newModuleDef();
    def->addInstance("i0",d,{{"ga",Const::make(c,6)},{"gb",Const::make(c,7)}},{{"ca",Const::make(c,11)},{"cb",Const::make(c,12)}});
    def->addInstance("i1",d,{{"gb",Const::make(c,7)}},{{"cb",Const::make(c,12)}});
  tester->setDef(def);
  tester->print();
 
  //run assertion checks
  checker(tester);
  
  deleteContext(c);
}


