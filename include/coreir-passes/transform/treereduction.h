#ifndef TREEREDUCTION_H_
#define TREEREDUCTION_H_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

//Start by inheriting from the predefined ModulePass
class TreeReduction : public ModulePass {
  
  vector<Instance*> targetSubgraphs;

  public:
    static std::string ID;

    //Note we are passing in "false" to the isAnalysis param.
    TreeReduction() : ModulePass(ID,"Finds associative operators joined together and replaces with tree implementation",false) {}

    bool runOnModule(Module* m) override;

    //Print function will output when in verbose mode.
    void print() override;

    //These are our class's custom APIs. We will be able to use this in 
    //other passes
    vector<Wireable*> collectInputs(Instance* head);
    vector<Instance*> collectInsts(Instance* head);
    bool isAssocSubgraph(Instance* i);
    Instance* getSelectedInst(Instance* i, string sel);
    string getOpName(Instance* i);
    int getTotalSubgraphs();
};

} // namespace passes
} // namespace coreir

#endif // TREEREDUCTION_H_
