#include "coreir.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  Type* inTp = c->BitInOut();

  cout << "Bit in out = " << inTp->toString() << endl;
  int width = 9;
  Type* muxType = c->Record({
    {"out", c->Bit()->Arr(width)},
    {"in0", c->BitIn()->Arr(width)},
    {"in1", c->BitIn()->Arr(width)},
    {"sel", c->BitIn()}
  });

  Namespace* g = c->getGlobal();
  Module* md = g->newModuleDecl("mux", muxType);
  ModuleDef* def = md->newModuleDef();

  def->addInstance("not0","corebit.not");
  def->addInstance("tp0","coreir.tribuf",{{"width",Const::make(c,width)}});
  def->addInstance("tp1","coreir.tribuf",{{"width",Const::make(c,width)}});
  def->addInstance("tg","coreir.ibuf",{{"width",Const::make(c,width)}});

  def->connect("self.sel", "not0.in");
  def->connect("self.sel", "tp1.en");
  def->connect("not0.out", "tp0.en");
  def->connect("self.in0", "tp0.in");
  def->connect("self.in1", "tp1.in");
  def->connect("tp0.out", "tg.in");
  def->connect("tp1.out", "tg.in");
  def->connect("tg.out", "self.out");
  
  md->setDef(def);
  md->print();
  

  deleteContext(c);
}
