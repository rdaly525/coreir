#include "coreir.h"
#include "coreir/passes/transform/wireclocks.h"

using namespace std;
using namespace CoreIR;

int testTuple() {
  Context* context = newContext();
  Namespace* global = context->getGlobal();
  // Namespace* prims = context->getNamespace("coreir");
  Type* clockType = context->Named("coreir.clk");
  Type* clockInType = context->Named("coreir.clkIn");

  Module* nested_clock_tuple = nullptr;
  if (!loadFromFile(
        context, "circuits/TestNestedClockTuple.json", &nested_clock_tuple)) {
    context->printerrors();
    return 1;
  }
  ModuleDef* definition = nested_clock_tuple->getDef();

  Passes::WireClocks* wireClock = new Passes::WireClocks(
    "wireclocks", clockInType);
  context->addPass(wireClock);

  // Run the pass
  context->runPasses({"wireclocks"});

  // Check that the clocks are now wired
  for (auto instance : definition->getInstances()) {
    Module* moduleRef = instance.second->getModuleRef();
    for (auto field : moduleRef->getType()->getRecord()) {
      if (isClockOrNestedClockType(field.second, clockType)) {
        ASSERT(
          instance.second->sel(field.first)->getConnectedWireables().size() > 0,
          "Wire Clock Pass Test Failed, not all clocks wired up.");
      }
    }
  }
  saveToFile(global, "_nested_clock_tuple_wired.json", nested_clock_tuple);
  deleteContext(context);
  return 0;
}

int testMultipleSIPO() {
  Context* context = newContext();
  Namespace* global = context->getGlobal();
  // Namespace* prims = context->getNamespace("coreir");
  Type* clockType = context->Named("coreir.clk");
  Type* clockInType = context->Named("coreir.clkIn");

  Module* multiple_sipo = nullptr;
  if (!loadFromFile(context, "circuits/multiple_sipo.json", &multiple_sipo)) {
    context->printerrors();
    return 1;
  }
  ModuleDef* definition = multiple_sipo->getDef();

  Passes::WireClocks* wireClock = new Passes::WireClocks(
    "wireclocks", clockInType);
  context->addPass(wireClock);

  // Run the pass
  context->runPasses({"wireclocks"});

  // Check that the clocks are now wired
  for (auto instance : definition->getInstances()) {
    Module* moduleRef = instance.second->getModuleRef();
    for (auto field : moduleRef->getType()->getRecord()) {
      if (isClockOrNestedClockType(field.second, clockType)) {
        ASSERT(
          instance.second->sel(field.first)->getConnectedWireables().size() > 0,
          "Wire Clock Pass Test Failed, not all clocks wired up.");
      }
    }
  }
  saveToFile(global, "_multiple_sipo_wired_clock.json", multiple_sipo);
  deleteContext(context);
  return 0;
}

int testShiftRegister() {
  Context* context = newContext();
  Namespace* global = context->getGlobal();
  // Namespace* prims = context->getNamespace("coreir");
  // Type* clockType = context->Named("coreir", "clk");
  Type* clockInType = context->Named("coreir.clkIn");

  Module* shift_register = nullptr;
  if (!loadFromFile(
        context,
        "circuits/shift_register_unwired_clock.json",
        &shift_register)) {
    context->printerrors();
    return 1;
  }
  // shift_register->print();
  ModuleDef* definition = shift_register->getDef();

  Passes::WireClocks* wireClock = new Passes::WireClocks(
    "wireclocks", clockInType);
  context->addPass(wireClock);

  // Run the pass
  context->runPasses({"wireclocks"});
  Wireable* topClock = definition->sel("self.clk");

  // Check that the clocks are now wired
  for (auto instance : definition->getInstances()) {
    ASSERT(
      definition->hasConnection(topClock, instance.second->sel("clk")),
      "Wire Clock Pass Test Failed, not all clocks wired up.");
  }
  saveToFile(global, "_shift_register_wired_clock.json", shift_register);
  deleteContext(context);
  return 0;
}

int main() { return testShiftRegister() || testMultipleSIPO() || testTuple(); }
