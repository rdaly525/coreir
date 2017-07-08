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

  // Define lb33 Module
  Type* lb33Type = c->Record({
    {"in",c->BitIn()->Arr(16)},
    {"out",c->Bit()->Arr(16)->Arr(3)->Arr(3)}
  });


  Module* lb33 = c->getGlobal()->newModuleDecl("lb33", lb33Type);
  ModuleDef* def = lb33->newModuleDef();
    def->addInstance("lb33_inst", linebuffer, {
      {"bitwidth",c->argInt(16)},
	    {"stencil_width",c->argInt(3)},
      {"stencil_height",c->argInt(3)},
			{"image_width",c->argInt(512)}
    });
    def->connect("self.in", "lb33_inst.in");
    def->connect("self.out", "lb33_inst.out");
  lb33->setDef(def);
  lb33->print();

  bool err = false;
  cout << "Checking saving and loading pregen" << endl;
  saveModule(lb33, "_lb33.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  loadModule(c,"_lb33.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  
  cout << "Running Generators" << endl;
  rungenerators(c,lb33,&err);
  if (err) c->die();
  lb33->print();
  Instance* i = cast<Instance>(lb33->getDef()->sel("lb33_inst"));
  i->getModuleRef()->print();

  cout << "Flattening everything" << endl;
  flatten(c,lb33,&err);
  lb33->print();
  lb33->getDef()->validate();
  
  cout << "Checking saving and loading postgen" << endl;
  saveModule(lb33, "_lb33Gen.json",&err);
  if (err) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }
  
  Module* m = loadModule(c,"_lb33Gen.json", &err);
  if(err) {
    cout << "Could not Load from json!!" << endl;
    c->die();
  }
  m->print();


  deleteContext(c);
}
