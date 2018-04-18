#include "coreir.h"
#include "coreir/libs/commonlib.h"

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
                     {{"width",Const::make(c,16)},{"N",Const::make(c,15)},{"operator",Const::make(c,"coreir.add")}}
                     );
    def->connect("self.in", "add15.in");
    def->connect("self.out", "add15.out");
  
  add15->setDef(def);
  //add15->print();
  c->runPasses({"rungenerators","flatten","verifyconnectivity-onlyinputs-noclkrst"});
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


  //Find bitopn in the common namespace
  Generator* bitopN = commonlib->getGenerator("bitopn");

  Type* bitadd15Type = c->Record({
        {"in",c->BitIn()->Arr(15)},
        {"out",c->Bit()}
      });

  Module* bitadd15 = c->getGlobal()->newModuleDecl("bitadd15", bitadd15Type);
  ModuleDef* defbit = bitadd15->newModuleDef();
    defbit->addInstance("bitadd15", bitopN, 
                     {{"N",Const::make(c,15)},{"operator",Const::make(c,"corebit.and")}}
                     );
    defbit->connect("self.in", "bitadd15.in");
    defbit->connect("self.out", "bitadd15.out");
  
  bitadd15->setDef(defbit);
  //bitadd15->print();
  c->runPasses({"rungenerators","flatten","verifyconnectivity-onlyinputs-noclkrst"});
  bitadd15->print();

  bitadd15->getDef()->validate();

  // write out the json
  cout << "Saving json" << endl;
  if (!saveToFile(c->getGlobal(), "_bitopn.json", bitadd15)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }

  // write out the dot file
  cout << "Saving dot file" << endl;
  if (!saveToDot(bitadd15, "_bitopn.txt")) {
    cout << "Could not save to dot!!" << endl;
    c->die();
  }

  
  CoreIR::Module* mbit = nullptr;
  if (!loadFromFile(c, "_bitopn.json", &mbit)) {
    cout << "Could not load from json!!" << endl;
    c->die();
  }
  ASSERT(mbit, "Could not load top: _bitopn");
  mbit->print();

  
  deleteContext(c);
}
