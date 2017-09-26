#include "coreir.h"

using namespace CoreIR;

class SimModule : public ModulePass {
  
  public:
    //The static keyword is important here!
    static std::string ID;
    //Note we are passing in "true" to the isAnalysis param.
    SimModule() : ModulePass(ID, "Generate simulation code", true) {}

  bool runOnModule(Module* m) override;

  //We get a print function that will print when we are in verbose mode.
  void print() override;


  // Add custom function to help with file output to output to stream
  // and move this to coreir/passes IGNORE FOR NOW
};
