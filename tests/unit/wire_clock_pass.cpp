#include "coreir.h"
#include "coreir-passes/common.h"

using namespace CoreIR;

int main() {
    Context* context = newContext();
    Namespace* global = context->getGlobal();
    // Namespace* prims = context->getNamespace("coreir");
    // Type* clockType = context->Named("coreir", "clk");
    Type* clockInType = context->Named("coreir", "clkIn");

    Module* shift_register = nullptr;
    if (!loadFromFile(context, "_shift_register_unwired_clock.json", &shift_register)) {
        context->printerrors();
        return 1;
    }
    shift_register->print();

    PassManager* passManager = new PassManager(global);
    WireClockPass* wireClock = new WireClockPass(clockInType);
    passManager->addPass(wireClock, 0);

    passManager->run();
    ModuleDef* definition = shift_register->getDef();
    Wireable* topClock = definition->sel("self.CLK");
    for (auto instance : definition->getInstances()) {
        ASSERT(definition->hasConnection(topClock, instance.second->sel("clk")), "Wire Clock Pass Test Failed, not all clocks wired up.");
    }

    deleteContext(context);
    return 0;
}
