#include "coreir.h"
#include "coreir/libs/commonlib.h"

using namespace std;
using namespace CoreIR;


int main() {
  
  // New context
  Context* c = newContext();
  
  //Find serializer in the commonlib namespace
  Namespace* commonlib = CoreIRLoadLibrary_commonlib(c);
  Generator* serializer = commonlib->getGenerator("serializer");

  // Define serial5 Module
  Type* serial5Type = c->Record({
    {"en",c->BitIn()},
    {"count",c->Bit()->Arr(16)},
    {"in",c->BitIn()->Arr(16)->Arr(5)},
    {"out",c->Bit()->Arr(16)}
  });


  Module* serial5 = c->getGlobal()->newModuleDecl("serial5", serial5Type);
  ModuleDef* def = serial5->newModuleDef();
  def->addInstance("serial5_inst", serializer, {{"width",Const::make(c,16)},{"rate",Const::make(c,5)}});
    def->connect("self.in", "serial5_inst.in");
    def->connect("self.out", "serial5_inst.out");
  serial5->setDef(def);
  serial5->print();

  cout << "Running Generators" << endl;
  serial5->print();

  //c->runPasses({"rungenerators", "flatten", "verifyconnectivity-onlyinputs-noclkrst"});
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
