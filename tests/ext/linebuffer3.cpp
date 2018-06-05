#include "coreir.h"
#include "coreir/libs/commonlib.h"

using namespace std;
using namespace CoreIR;


int main() {
  
  // New context
  Context* c = newContext();
  
  //Find linebuffer_3d in the commonlib namespace
  Namespace* commonlib = CoreIRLoadLibrary_commonlib(c);
  Generator* linebuffer3d = commonlib->getGenerator("linebuffer3d");

  // Define lb325 Module
  Type* lb325Type = c->Record({
    {"in",c->BitIn()->Arr(16)},
    {"out",c->Bit()->Arr(16)->Arr(3)->Arr(2)->Arr(5)}
  });


  Module* lb325 = c->getGlobal()->newModuleDecl("lb325", lb325Type);
  ModuleDef* def = lb325->newModuleDef();
  def->addInstance("lb325_inst", linebuffer3d, {{"bitwidth",Const::make(c,16)},
        {"stencil_d0",Const::make(c,3)},{"stencil_d1",Const::make(c,2)},{"stencil_d2",Const::make(c,5)},
                                         {"image_d0",Const::make(c,3)},{"image_d1",Const::make(c,512)}});
    def->connect("self.in", "lb325_inst.in");
    def->connect("self.out", "lb325_inst.out");
  lb325->setDef(def);
  //lb325->print();

  cout << "Running Generators" << endl;
  //lb325->print();

  c->runPasses({"rungenerators", "flatten"});
  lb325->getDef()->validate();

  // write out the json
  cout << "Saving json" << endl;
  if (!saveToFile(c->getGlobal(), "_lb325.json", lb325)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  CoreIR::Module* m = nullptr;
  if (!loadFromFile(c, "_lb325.json", &m)) {
    cout << "Could not load from json!!" << endl;
    c->die();
  }
  ASSERT(m, "Could not load top: _lb325");
  //m->print();


  deleteContext(c);
}
