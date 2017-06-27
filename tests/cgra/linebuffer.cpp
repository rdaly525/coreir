#include "coreir.h"
#include "coreir-lib/cgralib.h"
#include "coreir-lib/stdlib.h"
#include "coreir-pass/passes.h"


using namespace CoreIR;


int main() {
  
  // New context
  Context* c = newContext();
  CoreIRLoadLibrary_stdlib(c);
  
  //Find linebuffer in the cgra namespace
  Namespace* cgralib = CoreIRLoadLibrary_cgralib(c);
  Generator* linebuffer = cgralib->getGenerator("Linebuffer");

  // Define lb32 Module
  Type* lb32Type = c->Record({
    {"in",c->BitIn()->Arr(16)},
    {"out",c->Bit()->Arr(16)->Arr(2)->Arr(3)}
  });


  Module* lb32 = c->getGlobal()->newModuleDecl("lb32", lb32Type);
  ModuleDef* def = lb32->newModuleDef();
    def->addInstance("lb32_inst", linebuffer, {{"bitwidth",c->argInt(16)},
	  {"stencil_width",c->argInt(2)},{"stencil_height",c->argInt(3)},
					   {"image_width",c->argInt(512)}});
    def->connect("self.in", "lb32_inst.in");
    def->connect("self.out", "lb32_inst.out");
  lb32->setDef(def);
  lb32->print();

  bool err = false;
  cout << "Checking saving and loading pregen" << endl;
  saveModule(lb32, "_lb32.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  loadModule(c,"_lb32.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  
  cout << "Running Generators" << endl;
  rungenerators(c,lb32,&err);
  if (err) c->die();
  lb32->print();
  Instance* i = cast<Instance>(lb32->getDef()->sel("lb32_inst"));
  i->getModuleRef()->print();

  cout << "Flattening everything" << endl;
  flatten(c,lb32,&err);
  lb32->print();
  lb32->getDef()->validate();
  
  cout << "Checking saving and loading postgen" << endl;
  saveModule(lb32, "_lb32Gen.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  Module* m = loadModule(c,"_lb32Gen.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  m->print();


  deleteContext(c);
}
