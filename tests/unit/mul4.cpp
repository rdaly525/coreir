#include "coreir.h"
#include "coreir-lib/stdlib.h"
#include "coreir-pass/passes.h"

using namespace CoreIR;

int main() {
  uint n = 64;

  Context* c = newContext();

  Namespace* g = c->getGlobal();

  Namespace* stdlib = CoreIRLoadLibrary_stdlib(c);

  // Declare mul generator
  Generator* mul2 = stdlib->getGenerator("mul");
  assert(mul2);

  // Define mul4 module
  Type* mul4Type = c->Record({
      {"in", c->Array(4, c->Array(n, c->BitIn()))},
	{"out", c->Array(n, c->Bit())}
    });

  Module* mul4_n = g->newModuleDecl("Mul4", mul4Type);
  ModuleDef* def = mul4_n->newModuleDef();

  // Create wireables
  Wireable* self = def->sel("self");

  Wireable* mul_00 = def->addInstance("mul00", mul2, {{"width", c->argInt(n)}});
  Wireable* mul_01 = def->addInstance("mul01", mul2, {{"width", c->argInt(n)}});
  Wireable* mul_1 = def->addInstance("mul1", mul2, {{"width", c->argInt(n)}});

  def->connect(self->sel("in")->sel(0), mul_00->sel("in")->sel(0));
  def->connect(self->sel("in")->sel(1), mul_00->sel("in")->sel(1));

  def->connect(self->sel("in")->sel(2), mul_01->sel("in")->sel(0));
  def->connect(self->sel("in")->sel(3), mul_01->sel("in")->sel(1));

  def->connect(mul_00->sel("out"), mul_1->sel("in")->sel(0));
  def->connect(mul_01->sel("out"), mul_1->sel("in")->sel(1));

  def->connect(mul_1->sel("out"), self->sel("out"));

  mul4_n->setDef(def);
  mul4_n->print();

  bool err = false;

  cout << "Checking saving and loading pregen" << endl;
  saveModule(mul4_n, "_mul4.json", &err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }

  Module* m = loadModule(c, "_mul4.json", &err);
  if (err) {
    cout << "Could not load from json!!" << endl;
    c->die();
  }

  m->print();

  rungenerators(c, mul4_n, &err);
  if (err) {
    cout << "Error when calling rungenerators" << endl;
    c->die();
  }
  mul4_n->print();

  cout << "Checking saving and loading postgen" << endl;
  saveModule(mul4_n, "_mul4Gen.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  m = loadModule(c,"_mul4Gen.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  m->print();

  deleteContext(c);
  
  return 0;
  
}
