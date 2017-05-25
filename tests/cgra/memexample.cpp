#include "coreir.h"
#include "coreir-lib/cgralib.h"
#include "coreir-pass/passes.h"

using namespace CoreIR;

int main() {
  Context* c = newContext();

  Namespace* cgralib = CoreIRLoadLibrary_cgralib(c);
 
  //Createing a pretty expansive example for caleb
  Args w16 = {{"width",c->argInt(16)}};
  
  Generator* PE = cgralib->getGenerator("PE");
  Generator* IO = cgralib->getGenerator("IO");
  Generator* Mem = cgralib->getGenerator("Mem");
  Module* Top = c->getGlobal()->newModuleDecl("Top",c->Any());
  ModuleDef* def = Top->newModuleDef();
    def->addInstance("io0",IO,w16,{{"mode",c->argString("i")}});
    def->addInstance("p0",PE,{{"width",c->argInt(16)},{"numin",c->argInt(2)}},{{"op",c->argString("add")}});
  Params MemGenParams = {{"width",AINT},{"depth",AINT}};
    def->addInstance("m0",Mem,{{"width",c->argInt(16)},{"depth",c->argInt(512)}},{{"mode",c->argString("o")}});
    def->addInstance("p1",PE,{{"width",c->argInt(16)},{"numin",c->argInt(2)}},{{"op",c->argString("mult")}});
    def->addInstance("io1",IO,w16,{{"mode",c->argString("o")}});
    
    def->connect("io0.out","p0.data.in.0");
    def->connect("io0.out","m0.wdata");
    def->connect("p0.data.out","m0.addr");
    def->connect("p0.bit.out","m0.wen");
    def->connect("m0.full","p0.bit.in.0");

    def->connect("m0.rdata","io1.in");
    def->connect("m0.rdata","p1.data.in.0");
    def->connect("p1.bit.out","m0.ren");
    def->connect("m0.empty","p1.bit.in.0");

  Top->setDef(def);
  
  Top->print();
  
  bool err = false;
  //Save to Json
  cout << "Saving 2 json" << endl;
  saveModule(Top,"_mapped_memexample.json",&err);
  if(err) c->die();
  deleteContext(c);
  
  c = newContext();
  CoreIRLoadLibrary_cgralib(c);
  Module* m = loadModule(c,"_mapped_memexample.json",&err);
  if(err) c->die();
  m->print();  

  deleteContext(c);
  return 0;
}
