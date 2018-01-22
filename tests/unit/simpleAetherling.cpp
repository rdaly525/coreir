#include "coreir.h"
#include "coreir/libs/aetherlinglib.h"

using namespace std;
using namespace CoreIR;

int main() {
    Context* c = newContext();
    CoreIRLoadLibrary_aetherlinglib(c);

    //Type of module 
    Type* addmultType = c->Record({
            {"in",c->Array(16,c->BitIn())},
            {"out",c->Array(16,c->Bit())}
        });
    Values w16({{"width",Const::make(c,16)}});
    Module* addmult = c->getGlobal()->newModuleDecl("addmult",addmultType);
    ModuleDef* def = addmult->newModuleDef();

    Values mapNParams({
            {"width", Const::make(c, 16)},
            {"parallelOperators", Const::make(c, 4)},
            {"operator", Const::make(c, "coreir.mul")}
        });
                      
    // ignoring last argumen to addIstance as no module parameters    
    def->addInstance("mapMul", "aetherlinglib.mapN", mapNParams);

    def->connect("self.in","mapMul.in");
    def->connect("mapMul.out","self.out");
  
    addmult->print();
    cout << addmult->toString() << endl;
  
    deleteContext(c);
    return 0;
}
