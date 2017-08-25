#include "coreir.h"
using namespace CoreIR;

//Start by inheriting from the predefined ModulePass
class TreeReductionPass : public ModulePass {
  
  unordered_map<Wireable*,vector<Wireable*>> targetSubgraphs;

  public:
    static std::string ID;

    //Note we are passing in "true" to the isAnalysis param.
    TreeReductionPass() : ModulePass(ID,"Finds associative operators joined together and replaces with tree implementation",true) {}

    bool runOnModule(Module* m) override;

    //Print function will output when in verbose mode.
    void print() override;

    //These are our class's custom APIs. We will be able to use this in 
    //other passes
    vector<Wireable*> collectInputs(Instance* head);
    bool isAssocSubgraph(Instance* i);
    Instance* getSelectedInst(Instance* i, string sel);
    string getOpName(Instance* i);
    int getTotalSubgraphs();
};
