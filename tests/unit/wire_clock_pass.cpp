#include "coreir.h"
#include "coreir-passes/transform/wireclocks.h"

using namespace CoreIR;

int main() {
    Context* context = newContext();
    Namespace* global = context->getGlobal();
    // Namespace* prims = context->getNamespace("coreir");
    // Type* clockType = context->Named("coreir", "clk");
    Type* clockInType = context->Named("coreir", "clkIn");

    Module* shift_register = nullptr;
    if (!loadFromFile(context, "circuits/shift_register_unwired_clock.json", &shift_register)) {
        context->printerrors();
        return 1;
    }
    shift_register->print();

    Passes::WireClocks* wireClock = new Passes::WireClocks(clockInType);
    context->addPass(wireClock);

    context->runPasses({"wireclocks"});
    saveToFile(global, "_shift_register_wired_clock.json", shift_register);

    deleteContext(context);
    return 0;
}
