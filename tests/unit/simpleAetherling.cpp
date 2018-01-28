#include "coreir.h"
#include "coreir/libs/aetherlinglib.h"
#include <execinfo.h>
#include <stdio.h>
#include <signal.h>
#include <stdlib.h>
#include <unistd.h>



using namespace std;
using namespace CoreIR;

void handler(int sig) {
  void *array[10];
  size_t size;

  // get void*'s for all entries on the stack
  size = backtrace(array, 10);

  // print out all the frames to stderr
  fprintf(stderr, "Error: signal %d:\n", sig);
  backtrace_symbols_fd(array, size, STDERR_FILENO);
  exit(1);
}

int main() {
    signal(SIGSEGV, handler);   // install our handler
    Context* c = newContext();
    CoreIRLoadLibrary_aetherlinglib(c);

    //Type of module 
    Type* oneInOneOutGenType = c->Record({
            {"in",c->Array(16,c->BitIn())},
            {"out",c->Array(16,c->Bit())}
        });
    Module* testModule = c->getGlobal()->newModuleDecl("testModule",oneInOneOutGenType);
    ModuleDef* testDef = testModule->newModuleDef();

    /* creating the mulBy2 that the mapN will parallelize */
    Module* mulBy2 = c->getGlobal()->newModuleDecl("mulBy2", oneInOneOutGenType);
    ModuleDef* mulBy2Def = mulBy2->newModuleDef();

    uint width = 16;
    string constModule = Aetherling_addCoreIRConstantModule(c, mulBy2Def, width, Const::make(c, width, 4));
    mulBy2Def->addInstance("mul", "coreir.mul", {{"width", Const::make(c, width)}});
    mulBy2Def->connect("self.in", "mul.in0");
    mulBy2Def->connect(constModule + ".out", "mul.in1");
    mulBy2Def->connect("mul.out", "self.out");

    Values mapNParams({
            {"width", Const::make(c, width)},
            {"parallelOperators", Const::make(c, 4)},
            {"operator", Const::make(c, mulBy2)}
        });
                      
    // ignoring last argumen to addIstance as no module parameters    
    testDef->addInstance("mapMul", "aetherlinglib.mapN", mapNParams);

    testDef->connect("self.in","mapMul.in");
    testDef->connect("mapMul.out","self.out");

    c->runPasses({"rungenerators", "verifyconnectivity"});
  
    testModule->print();
    cout << testModule->toString() << endl;
  
    deleteContext(c);
    return 0;
}
