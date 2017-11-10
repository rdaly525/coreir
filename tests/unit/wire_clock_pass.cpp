#include "coreir.h"
#include "coreir/passes/transform/wireclocks.h"

using namespace std;
using namespace CoreIR;

int main() {
    Context* context = newContext();
    Namespace* global = context->getGlobal();
    // Namespace* prims = context->getNamespace("coreir");
    // Type* clockType = context->Named("coreir", "clk");
    Type* clockInType = context->Named("coreir.clkIn");

    Module* shift_register = nullptr;
    if (!loadFromFile(context, "circuits/shift_register_unwired_clock.json", &shift_register)) {
        context->printerrors();
        return 1;
    }
    // shift_register->print();
    ModuleDef* definition = shift_register->getDef();

    Passes::WireClocks* wireClock = new Passes::WireClocks("wireclocks",clockInType);
    context->addPass(wireClock);

    // Run the pass
    context->runPasses({"wireclocks"});
    Wireable* topClock = definition->sel("self.clk");

    // Check that the clocks are now wired
    for (auto instance : definition->getInstances()) {
        ASSERT(definition->hasConnection(topClock, instance.second->sel("clk")), 
               "Wire Clock Pass Test Failed, not all clocks wired up.");
    }
    saveToFile(global, "_shift_register_wired_clock.json", shift_register);

    deleteContext(context);
    return 0;
}
