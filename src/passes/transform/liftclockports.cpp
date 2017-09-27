#include "coreir.h"
#include "coreir/passes/transform/liftclockports.h"

using namespace std;
using namespace CoreIR;

bool Passes::LiftClockPorts::runOnInstanceGraphNode(InstanceGraphNode& node) {
    Instantiable* instantiable = node.getInstantiable();
    bool clockAdded = false;
    
    if (isa<Generator>(instantiable)) return false;
    Module* module = cast<Module>(instantiable);
    if (!module->hasDef()) return false;

    ModuleDef* definition = module->getDef();
    RecordType* type = cast<RecordType>(definition->getType());  // FIXME: Can I assume this is always a RecordType
    bool containsClock = false;
    for (auto field : type->getRecord()) {
        if (field.second == this->clockType) {
            containsClock = true;
            break;
        }
    }
    if (!containsClock) {
        bool addClock = false;
        for (auto instance : definition->getInstances()) {
            RecordType* instanceType = cast<RecordType>(instance.second->getType());
            for (auto field : instanceType->getRecord()) {
                if (field.second == this->clockType) {
                    addClock = true;
                    break;
                }
            }
            if (addClock) break;
        }
        if (addClock) {
            node.appendField("clk", this->clockType);
            clockAdded = true;
        }
    }

    return clockAdded;
}
