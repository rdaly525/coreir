#include "coreir.h"
#include "coreir/libs/commonlib.h"

using namespace std;
using namespace CoreIR;


int main() {
  
  // New context
  Context* c = newContext();
  
  //Find linebuffer in the commonlib namespace
  Namespace* commonlib = CoreIRLoadLibrary_commonlib(c);
  Generator* linebuffer = commonlib->getGenerator("linebuffer");

  // input stream and output stencil for arr(x)->arr(y)->arr(z) 
  //                             have size x horiz, y vert, z depth
  Type* in_type = c->BitIn()->Arr(16)->Arr(2)->Arr(2);
  Type* out_type = c->Bit()->Arr(16)->Arr(6)->Arr(6);
  Type* img_type = c->Bit()->Arr(16)->Arr(48)->Arr(48);

//  Type* in_type = c->BitIn()->Arr(16)->Arr(2)->Arr(1);
//  Type* out_type = c->Bit()->Arr(16)->Arr(4)->Arr(3);
//  Type* img_type = c->Bit()->Arr(16)->Arr(48)->Arr(48);

//  Type* in_type = c->BitIn()->Arr(16)->Arr(1)->Arr(2)->Arr(1);
//  Type* out_type = c->Bit()->Arr(16)->Arr(3)->Arr(4)->Arr(2);
//  Type* img_type = c->Bit()->Arr(16)->Arr(48)->Arr(48)->Arr(96);

  // Define lb32 Module
  Type* lb32Type = c->Record({
			{"in",in_type},
			{"wen",c->BitIn()}, 
      //{"valid", c->Bit()},
			{"out",out_type}
  });


  // REGULAR CASE (image width != stencil width) and 2D

  Module* lb32 = c->getGlobal()->newModuleDecl("lb32", lb32Type);
  ModuleDef* def = lb32->newModuleDef();
  def->addInstance("lb32_inst", linebuffer, {{"input_type",Const::make(c,in_type)}, 
        {"output_type",Const::make(c,out_type)}, {"image_type",Const::make(c,img_type)}});
    def->connect("self", "lb32_inst");
  lb32->setDef(def);
  lb32->print();

  cout << "Running Generators" << endl;
  //lb32->print();
  c->runPasses({"rungenerators"});
  if (!saveToFile(c->getGlobal(), "_linebuffer.json", lb32)) {
    cout << "Could not save to json!!" << endl;
  }

  cout << "Validating!!" << endl;
  lb32->getDef()->validate();
  cout << "1validated :(" << endl;
  c->runPasses({"verifyconnectivity-onlyinputs-noclkrst"},{"global","commonlib","memory","mantle"});
  cout << "2validated :(" << endl;
  c->runPasses({"flatten"});
  cout << "flattned :(" << endl;
  c->runPasses({"verifyconnectivity-onlyinputs-noclkrst"});
  //lb32->getDef()->validate();
  cout << "3validated :(" << endl;
  //c->runPasses({"rungenerators","verifyconnectivity-noclkrst"});
  //c->runPasses({"rungenerators", "flatten","verifyconnectivity-onlyinputs-noclkrst"});
  //lb32->print();
  lb32->getDef()->validate();

  // write out the json
  cout << "Saving json" << endl;
  if (!saveToFile(c->getGlobal(), "_linebuffer.json", lb32)) {
    cout << "Could not save to json!!" << endl;
    c->die();
  }

  // write out the dot file
  cout << "Saving dot file" << endl;
  if (!saveToDot(lb32, "_linebuffer.txt")) {
    cout << "Could not save to dot!!" << endl;
    c->die();
  }
  
  CoreIR::Module* m = nullptr;
  if (!loadFromFile(c, "_linebuffer.json", &m)) {
    cout << "Could not load from json!!" << endl;
    c->die();
  }
  ASSERT(m, "Could not load top: _linebuffer");
  //m->print();

  // SPECIAL CASE (stencil width == image width)
  /*
  Const* aImageW2 = Const::make(c,2);

  Module* lb32_special = c->getGlobal()->newModuleDecl("lb32_special", lb32Type);
  ModuleDef* def2 = lb32_special->newModuleDef();
    def2->addInstance("lb32_special_inst", linebuffer, {{"bitwidth",aWidth},
	  {"stencil_width",aStencilW},{"stencil_height",aStencilH},
					   {"image_width",aImageW2}});
    def2->connect("self.in", "lb32_special_inst.in");
    def2->connect("self.out", "lb32_special_inst.out");
  lb32_special->setDef(def2);
  lb32_special->print();

  cout << "Running Generators" << endl;
  lb32_special->print();

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
  m->print();
  */

  deleteContext(c);
}
