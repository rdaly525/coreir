#include "coreir.h"
#include "coreir-lib/cgralib.h"
#include "coreir-pass/passes.hpp"

using namespace CoreIR;

int main() {
  Context* c = newContext();

  Namespace* cgralib = CoreIRLoadLibrary_cgralib(c);
 
  //Createing a pretty expansive example for caleb
  Args w16 = {{"width",c->argInt(16)}};
  
  Generator* PE = cgralib->getGenerator("PE");
  Generator* IO = cgralib->getGenerator("IO");
  Generator* Reg = cgralib->getGenerator("Reg");
  Generator* Const = cgralib->getGenerator("Const");
  Module* Top = c->getGlobal()->newModuleDecl("Top",c->Any());
  ModuleDef* def = Top->newModuleDef();
    def->addInstance("io0",IO,w16,{{"mode",c->argString("i")}});
    def->addInstance("r0",Reg,w16);
    def->addInstance("c0",Const,w16,{{"value",c->argInt(795)}});
    def->addInstance("p0",PE,{{"width",c->argInt(16)},{"numin",c->argInt(2)}},{{"op",c->argString("add")}});
    def->addInstance("r1",Reg,w16);
    def->addInstance("r2",Reg,w16);
    def->addInstance("r3",Reg,w16);
    def->addInstance("r4",Reg,w16);
    def->addInstance("io1",IO,w16,{{"mode",c->argString("o")}});
    
    def->wire("io0.out","r0.in");
    def->wire("c0.out","p0.data.in.0");
    def->wire("r0.out","p0.data.in.1");
    def->wire("p0.data.out","r1.in");
    def->wire("r1.out","r2.in");
    def->wire("r2.out","r3.in");
    def->wire("r3.out","r4.in");
    def->wire("r4.out","io1.in");
  Top->setDef(def);
  
  Top->print();
  
  bool err = false;
  //Save to Json
  cout << "Saving 2 json" << endl;
  saveModule(Top,"_mapped_regexample.json",&err);
  if(err) c->die();
  deleteContext(c);
  cout << "H7\n";
  c = newContext();
  CoreIRLoadLibrary_cgralib(c);
  Module* m = loadModule(c,"_mapped_regexample.json",&err);
  if(err) c->die();
  m->print();

  deleteContext(c);
  return 0;
}
