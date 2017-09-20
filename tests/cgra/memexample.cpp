#include "coreir.h"
#include "coreir/libs/cgralib.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  Namespace* cgralib = CoreIRLoadLibrary_cgralib(c);
 
  //Createing a pretty expansive example for caleb
  Args w16 = {{"width",Const(16)}};
  
  Generator* PE = cgralib->getGenerator("PE");
  Generator* IO = cgralib->getGenerator("IO");
  Generator* Mem = cgralib->getGenerator("Mem");
  Module* Top = c->getGlobal()->newModuleDecl("Top",c->Record());
  ModuleDef* def = Top->newModuleDef();
    def->addInstance("io0",IO,w16,{{"mode",Const("i")}});
    def->addInstance("p0",PE,{{"width",Const(16)}},{{"op",Const("add")}});
  Params MemGenParams = {{"width",AINT},{"depth",AINT}};
    def->addInstance("m0",Mem,{{"width",Const(16)},{"depth",Const(512)}},{{"mode",Const("o")}});
    def->addInstance("p1",PE,{{"width",Const(16)}},{{"op",Const("mult")}});
    def->addInstance("io1",IO,w16,{{"mode",Const("o")}});
    
    def->connect("io0.out","p0.data.in.0");
    def->connect("io0.out","m0.wdata");
    def->connect("p0.data.out","m0.addr");
    def->connect("p0.bit.out","m0.wen");
    def->connect("m0.almost_full","p0.bit.in.0");

    def->connect("m0.rdata","io1.in");
    def->connect("m0.rdata","p1.data.in.0");
    def->connect("p1.bit.out","m0.ren");
    def->connect("m0.valid","p1.bit.in.0");

  Top->setDef(def);
  
  Top->print();
  
  deleteContext(c);
  return 0;
}
