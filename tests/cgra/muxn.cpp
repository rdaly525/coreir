#include "coreir.h"
#include "coreir/libs/commonlib.h"

using namespace std;
using namespace CoreIR;

int main() {
  
  // New context
  Context* c = newContext();
  
  //Find muxn in the common namespace
  Namespace* commonlib = CoreIRLoadLibrary_commonlib(c);
  Generator* muxn = commonlib->getGenerator("muxn");

  // Define muxN Module
  uint N = 10;
  Type* muxNType = c->Record({
      {"in",c->Record({
            {"data",c->BitIn()->Arr(16)->Arr(N)},
            {"sel",c->BitIn()->Arr(4)}
          })},
    {"out",c->Bit()->Arr(16)}
  });


  Module* muxN = c->getGlobal()->newModuleDecl("mux_n", muxNType);
  ModuleDef* def = muxN->newModuleDef();
    def->addInstance("muxN_inst", muxn, 
                     {{"width",Const::make(c,16)},{"N",Const::make(c,N)}});
    def->connect("self.in", "muxN_inst.in");
    def->connect("self.out", "muxN_inst.out");
  muxN->setDef(def);
  muxN->print();

  c->runPasses({"rungenerators", "flatten", "verifyconnectivity-noclkrst"});
  muxN->getDef()->validate();

  // write out the json
  cout << "Saving json" << endl;
  if (!saveToFile(c->getGlobal(), "_muxn.json", muxN)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  CoreIR::Module* m = nullptr;
  if (!loadFromFile(c, "_muxn.json", &m)) {
    cout << "Could not load from json!!" << endl;
    c->die();
  }
  ASSERT(m, "Could not load top: _muxn");
  m->print();
    
  deleteContext(c);
}
