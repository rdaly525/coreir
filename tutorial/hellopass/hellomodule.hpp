
/*
 * Now we are going to write a simple Module Pass
 * Module Passes run only in the context of a Module.
 * This Pass is analogous to LLVM's Function Pass.
 *
 * Module Passes are not allowed to make changes to anything outside
 * of the current Module. There are also no guarentees about the order
 * of the modules which you are running on.
 *
 * Lets make a pass that keeps track information about which modules have
 * registers As you will see in the next example, we can use this information in
 * another pass! Any Pass that can be used by other passes is called an Analysis
 * pass.
 */

#include "coreir.h"
using namespace CoreIR;

// Start by inheriting from the predefined ModulePass
class HelloModule : public ModulePass {

  // Lets define some custom data structure.
  // This will keep a map from modules to a list of its register instances
  unordered_map<Instantiable*, vector<Instance*>> registerMap;

 public:
  // Note we are passing in "true" to the isAnalysis param.
  HelloModule() : ModulePass("hellomodule", "Descritpion Blah Blah", true) {}
  bool runOnModule(Module* m) override;
  // We get a print function that will print when we are in verbose mode.
  void print() override;

  // These are our class's custom APIs. We will be able to use this in
  // other passes
  bool hasRegisterInstances(Instantiable* i);
  std::vector<Instance*> getRegisterInstances(Instantiable* i);
  int getTotalRegisters();
};
