#include "coreir.h"
#include "coreir-lib/commonlib.h"

using namespace std;
using namespace CoreIR;

int main() {
  
  // New context
  Context* c = newContext();
  
  //Find opn in the common namespace
  Namespace* commonlib = CoreIRLoadLibrary_commonlib(c);
  Generator* opN = commonlib->getGenerator("opn");

  Type* add15Type = c->Record({
        {"in",c->BitIn()->Arr(16)->Arr(15)},
        {"out",c->Bit()->Arr(16)}
      });

  Module* add15 = c->getGlobal()->newModuleDecl("add15", add15Type);
  ModuleDef* def = add15->newModuleDef();
    def->addInstance("add15", opN, 
                     {{"width",c->argInt(16)},{"N",c->argInt(15)},{"operator",c->argString("coreir.add")}}
                     );
    def->connect("self.in", "add15.in");
    def->connect("self.out", "add15.out");
  
  add15->setDef(def);
  //add15->print();
  c->runPasses({"rungenerators","flatten"});
  add15->print();

  add15->getDef()->validate();

  // write out the json
  cout << "Saving json" << endl;
  if (!saveToFile(c->getGlobal(), "_opn.json", add15)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  CoreIR::Module* m = nullptr;
  if (!loadFromFile(c, "_opn.json", &m)) {
    cout << "Could not load from json!!" << endl;
    c->die();
  }
  ASSERT(m, "Could not load top: _opn");
  m->print();
    
  deleteContext(c);
}
