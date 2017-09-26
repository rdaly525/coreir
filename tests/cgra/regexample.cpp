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
    def->addInstance("r0","coreir.reg",w16);
    def->addInstance("c0","coreir.const",w16,{{"value",Const(795)}});
    def->addInstance("p0","cgralib.PE",Args(),{{"op_kind",Const("combined")},{"alu_op",Const("add")}});
    def->addInstance("r1","coreir.reg",w16);
    def->addInstance("r2","coreir.reg",w16);
    def->addInstance("r3","coreir.reg",w16);
    def->addInstance("r4","coreir.reg",w16);
    def->addInstance("io1","cgralib.IO",w16,{{"mode",Const("o")}});
    
    def->connect("io0.out","r0.in");
    def->connect("c0.out","p0.data.in.0");
    def->connect("r0.out","p0.data.in.1");
    def->connect("p0.data.out","r1.in");
    def->connect("r1.out","r2.in");
    def->connect("r2.out","r3.in");
    def->connect("r3.out","r4.in");
    def->connect("r4.out","io1.in");
  Top->setDef(def);
  
  Top->print();

  deleteContext(c);
  return 0;
}
