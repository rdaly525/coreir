#include "coreir.h"
#include "coreir-passes/transform/wireclocks.h"

using namespace CoreIR;

std::string Passes::WireClocks::ID = "wireclocks";
bool Passes::WireClocks::runOnModule(Module* module) {
    ASSERT(module->hasDef(), "WireClockPass can only be run on a module with a definition");

    ModuleDef* definition = module->getDef();

    RecordType* type = (RecordType*) definition->getType();  // FIXME: Can I assume this is always a RecordType
    string clkInName;
    for (auto field : type->getRecord()) {
        if (field.second == this->clockType) {
            ASSERT(clkInName.empty(), "Found multiple inputs with the same clock type in wireclockpass");
            clkInName = field.first;
            break;
        }
    }
    Interface* interface = definition->getInterface();
    Wireable* interfaceClock = interface->sel(clkInName);

    bool clockWired = false;
    for (auto instance : definition->getInstances()) {
        RecordType* instanceType = (RecordType*) instance.second->getType();
        for (auto field : instanceType->getRecord()) {
            std::cout << field.first << std::endl;
            if (field.second == this->clockType) {
                definition->connect(interfaceClock, instance.second->sel(field.first));
                clockWired = true;
                break;
            }
        }
    }
    return clockWired;
}
