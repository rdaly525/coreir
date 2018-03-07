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

    uint parallelInputs = 4;
    uint inputWidth = 8;

    Type* allInputsType = c->BitIn()->Arr(inputWidth)->Arr(parallelInputs);
    
    //Type of module 
    Type* oneInManyOutGenType = c->Record({
            {"in", allInputsType},
            {"out", c->Out(allInputsType)},
            {"en", c->BitIn()},
            {"ready", c->Bit()},
            {"valid", c->Bit()},
            {"reset", c->BitIn()},
            {"count", c->Bit()->Arr(inputWidth)}
        });
    Module* testModule = c->getGlobal()->newModuleDecl("testModule",oneInManyOutGenType);
    ModuleDef* testDef = testModule->newModuleDef();

    Values serializerParams{
        {"rate", Const::make(c, parallelInputs)},
        {"width", Const::make(c, inputWidth)}
    };

    testDef->addInstance("serializer", "commonlib.serializer", serializerParams);
    testDef->addInstance("deserializer", "commonlib.deserializer", serializerParams);

    testDef->connect("self.in", "serializer.in");
    testDef->connect("serializer.out", "deserializer.in");
    testDef->connect("deserializer.out", "self.out");
    testDef->connect("self.en", "serializer.en");
    testDef->connect("self.en", "deserializer.en");
    testDef->connect("self.reset", "serializer.reset");
    testDef->connect("self.reset", "deserializer.reset");
    testDef->connect("serializer.ready", "self.ready");
    testDef->connect("deserializer.valid", "self.valid");
    testDef->connect("serializer.count", "self.count");
    
    testModule->setDef(testDef);
    testModule->print();
    c->runPasses({"rungenerators", "verifyconnectivity"});
  
    testModule->print();
    cout << testModule->toString() << endl;
  
    deleteContext(c);
    return 0;
}
