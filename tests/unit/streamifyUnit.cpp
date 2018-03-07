#include "coreir.h"
#include "coreir/libs/aetherlinglib.h"
#include "coreir/libs/commonlib.h"
#include <execinfo.h>
#include <stdio.h>
#include <signal.h>
#include <stdlib.h>
#include <unistd.h>
#include <math.h>



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
    CoreIRLoadLibrary_commonlib(c);
    CoreIRLoadLibrary_aetherlinglib(c);

    uint parallelInputs = 4;
    uint inputWidth = 8;

    Type* twoArrays = c->Record({
                    {"container",c->Record({
                                {"el1", c->BitIn()->Arr(inputWidth)},
                                {"el0", c->BitIn()->Arr(inputWidth)}
                            })}
                });
    
    //Type of module 
    Type* oneInManyOutGenType = c->Record({
            {"in", twoArrays->Arr(parallelInputs)},
            {"out", c->Out(twoArrays->Arr(parallelInputs))},
            {"en", c->BitIn()},
            {"ready", c->Bit()},
            {"valid", c->Bit()},
            {"reset", c->BitIn()}
        });
    Module* testModule = c->getGlobal()->newModuleDecl("testModule",oneInManyOutGenType);
    ModuleDef* testDef = testModule->newModuleDef();

    Values streamifyParams{
        {"arrayLength", Const::make(c, parallelInputs)},
        {"elementType", Const::make(c, twoArrays)}
    };

    testDef->addInstance("streamify", "aetherlinglib.streamify", streamifyParams);
    testDef->addInstance("arrayify", "aetherlinglib.arrayify", streamifyParams);

    testDef->connect("self.in", "streamify.in");
    testDef->connect("streamify.out", "arrayify.in");
    testDef->connect("arrayify.out", "self.out");
    testDef->connect("self.en", "streamify.en");
    testDef->connect("self.en", "arrayify.en");
    testDef->connect("self.reset", "streamify.reset");
    testDef->connect("self.reset", "arrayify.reset");
    testDef->connect("streamify.ready", "self.ready");
    testDef->connect("arrayify.valid", "self.valid");
    
    testModule->setDef(testDef);
    testModule->print();
    c->runPasses({"rungenerators", "verifyconnectivity"});
  
    testModule->print();
  
    deleteContext(c);
    return 0;
}
