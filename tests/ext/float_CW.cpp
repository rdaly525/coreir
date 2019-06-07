#include "coreir.h"

using namespace std;
using namespace CoreIR;


int main() {
  
  // New context
  Context* c = newContext();

  // Define serial5 Module
  Type* serial5Type = c->Record({
    {"en",c->BitIn()},
    {"count",c->Bit()->Arr(16)},
    {"in",c->BitIn()->Arr(16)->Arr(5)},
    {"out",c->Bit()->Arr(16)}
  });

  c->getLibraryManager()->loadLib("float");
  c->getLibraryManager()->loadLib("float_CW");
  auto app = c->getGlobal()->newModuleDecl("app", c.Record({}));
  auto def = app->newModuleDef();


  Args bfloatArgs({{"exp_bits",Const::make(c,8)},{"frac_bits",Const::make(c,7)},{"ieee_compliance",Const::make(c,false)}});
  auto add = def->addInstance("add","fp.add",bfloatArgs);
  auto mul = def->addInstance("mul","fp.mul",bfloatArgs);
  def->connect(add->sel("out"),mul->sel("in0"));
  
  cout << "Running Generators" << endl;
  serial5->print();

  c->runPasses({"rungenerators", "flatten"});
  serial5->getDef()->validate();

  // write out the json
  cout << "Saving json" << endl;
  if (!saveToFile(c->getGlobal(), "_serial5.json", serial5)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  CoreIR::Module* m = nullptr;
  if (!loadFromFile(c, "_serial5.json", &m)) {
    cout << "Could not load from json!!" << endl;
    c->die();
  }
  ASSERT(m, "Could not load top: _serial5");
  m->print();


  deleteContext(c);
}
