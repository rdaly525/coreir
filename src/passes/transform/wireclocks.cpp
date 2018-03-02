#include "coreir.h"
#include "coreir/passes/transform/wireclocks.h"

using namespace std;
using namespace CoreIR;

bool Passes::WireClocks::runOnInstanceGraphNode(InstanceGraphNode& node) {
    
    Module* module = node.getModule();
    if (!module->hasDef()) return false;

    ModuleDef* def = module->getDef();
    vector<Wireable*> clks;
    //Check if any instance has a clock type
    for (auto inst : def->getInstances()) {
      for (auto field : cast<RecordType>(inst.second->getType())->getRecord()) {
        if (field.second == this->clockType) {
          clks.push_back(inst.second->sel(field.first));
        }
      }
    }
    if (clks.size()==0) {
      return false;
    }
    
    Wireable* topclk=nullptr;
    for (auto field : module->getType()->getRecord()) {
      if (field.second == this->clockType) {
        topclk = def->sel("self")->sel(field.first);
      }
    }
    //Add clk if needed
    if (!topclk) {
      node.appendField("clk", this->clockType);
      topclk = def->sel("self")->sel("clk");
    }
    for (auto clk : clks) {
      if (!def->hasConnection(topclk,clk)) {
        def->connect(topclk,clk);
      }
    }

    return true;
}
