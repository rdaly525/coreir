#include "coreir.h"
#include "coreir/libs/commonlib.h"

using namespace std;
using namespace CoreIR;


int main() {
  
  // New context
  Context* c = newContext();
  
  //Find linebuffer in the commonlib namespace
  Namespace* commonlib = CoreIRLoadLibrary_commonlib(c);
  Generator* linebuffer = commonlib->getGenerator("linebuffer2d");

  // Define lb32 Module
  Type* lb32Type = c->Record({
    {"in",c->BitIn()->Arr(16)},
    {"out",c->Bit()->Arr(16)->Arr(2)->Arr(3)}
  });

  // REGULAR CASE (image width != stencil width)

  Const* aWidth = Const::make(c,16);
  Const* aStencilW = Const::make(c,2);
  Const* aStencilH = Const::make(c,3);
  Const* aImageW = Const::make(c,512);

  Module* lb32 = c->getGlobal()->newModuleDecl("lb32", lb32Type);
  ModuleDef* def = lb32->newModuleDef();
    def->addInstance("lb32_inst", linebuffer, {{"bitwidth",aWidth},
          {"stencil_width",aStencilW},{"stencil_height",aStencilH},
                                        {"image_width",aImageW}});
    def->connect("self.in", "lb32_inst.in");
    def->connect("self.out", "lb32_inst.out");
  lb32->setDef(def);
  //lb32->print();

  cout << "Running Generators" << endl;
  //lb32->print();

  c->runPasses({"rungenerators", "flatten"});
  lb32->getDef()->validate();

  // write out the json
  cout << "Saving json" << endl;
  if (!saveToFile(c->getGlobal(), "_lb32.json", lb32)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  CoreIR::Module* m = nullptr;
  if (!loadFromFile(c, "_lb32.json", &m)) {
    cout << "Could not load from json!!" << endl;
    c->die();
  }
  ASSERT(m, "Could not load top: _lb32");
  //m->print();

  // SPECIAL CASE (stencil width == image width)

  Const* aImageW2 = Const::make(c,2);

  Module* lb32_special = c->getGlobal()->newModuleDecl("lb32_special", lb32Type);
  ModuleDef* def2 = lb32_special->newModuleDef();
    def2->addInstance("lb32_special_inst", linebuffer, {{"bitwidth",aWidth},
	  {"stencil_width",aStencilW},{"stencil_height",aStencilH},
					   {"image_width",aImageW2}});
    def2->connect("self.in", "lb32_special_inst.in");
    def2->connect("self.out", "lb32_special_inst.out");
  lb32_special->setDef(def2);
  //lb32_special->print();

  cout << "Running Generators" << endl;
  //lb32_special->print();

  c->runPasses({"rungenerators", "flatten"});
  lb32_special->getDef()->validate();

  // write out the json
  cout << "Saving json" << endl;
  if (!saveToFile(c->getGlobal(), "_lb32_special.json", lb32_special)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  CoreIR::Module* m2 = nullptr;
  if (!loadFromFile(c, "_lb32_special.json", &m2)) {
    cout << "Could not load from json!!" << endl;
    c->die();
  }
  ASSERT(m, "Could not load top: _lb32_special");
  //m->print();




  deleteContext(c);
}
