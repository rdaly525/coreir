#include "coreir.h"
#include "coreir/passes/transform/wireclocks.h"

using namespace std;
using namespace CoreIR;

bool Passes::WireClocks::runOnModule(Module* module) {

    ModuleDef* definition = module->getDef();

    RecordType* type = cast<RecordType>(definition->getType());  // FIXME: Can I assume this is always a RecordType
    string clkInName="";
    for (auto field : type->getRecord()) {
        if (field.second == this->clockType) {
            ASSERT(clkInName.empty(), "Found multiple inputs with the same clock type in wireclockpass");
            clkInName = field.first;
            break;
        }
    }
    if (clkInName=="") return false;
    Interface* interface = definition->getInterface();
    Wireable* interfaceClock = interface->sel(clkInName);

    bool clockWired = false;
    for (auto instance : definition->getInstances()) {
        RecordType* instanceType = cast<RecordType>(instance.second->getType());
        for (auto field : instanceType->getRecord()) {
            if (field.second == this->clockType) {
                if (!definition->hasConnection(interfaceClock, instance.second->sel(field.first))) {
                    definition->connect(interfaceClock, instance.second->sel(field.first));
                    clockWired = true;
                    break;
                }
            }
        }
    }
    return clockWired;
}
