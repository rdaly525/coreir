#include "coreir.h"
#include "coreir/libs/cgralib.h"

using namespace std;
using namespace CoreIR;

int main() {
  Context* c = newContext();

  CoreIRLoadLibrary_cgralib(c);
 
  //Createing a pretty expansive example for caleb
  Args w16 = {{"width",Const(16)}};
  
  Module* Top = c->getGlobal()->newModuleDecl("Top",c->Record());
  ModuleDef* def = Top->newModuleDef();
    def->addInstance("io0","cgralib.IO",w16,{{"mode",Const("i")}});
    def->addInstance("p0","cgralib.PE",Args(),{{"op_kind",Const("combined")},{"alu_op",Const("add")}});
    def->addInstance("m0","cgralib.Mem",Args(),{{"mode",Const("o")}});
    def->addInstance("p1","cgralib.PE",Args(),{{"op_kind",Const("combined")},{"alu_op",Const("mult")}});
    def->addInstance("io1","cgralib.IO",w16,{{"mode",Const("o")}});
    
    def->connect("io0.out","p0.data.in.0");
    def->connect("io0.out","m0.wdata");
    def->connect("p0.data.out","m0.raddr");
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
