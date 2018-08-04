#include "coreir.h"
#include "coreir/passes/transform/wireclocks.h"

using namespace std;
using namespace CoreIR;


void Passes::WireClocks::connectClk(ModuleDef* def, Wireable* topClk, Wireable* clk) {
    if (auto arrayType = dyn_cast<ArrayType>(clk->getType())) {
        for (int i = 0; i < arrayType->getLen(); i++) {
          this->connectClk(def, topClk, clk->sel(i));
        }
    } else if (!def->hasClockConnection(topClk, clk)) {
        def->connect(topClk,clk);
    }
}

bool Passes::WireClocks::runOnInstanceGraphNode(InstanceGraphNode& node) {
    
    Module* module = node.getModule();
    if (!module->hasDef()) return false;

    ModuleDef* def = module->getDef();
    vector<Wireable*> clks;
    //Check if any instance has a clock type
    for (auto inst : def->getInstances()) {
      for (auto field : cast<RecordType>(inst.second->getType())->getRecord()) {
        if (isClockOrNestedClockType(field.second, this->clockType)) {
          clks.push_back(inst.second->sel(field.first));
        }
      }
    }
    if (clks.size()==0) {
      return false;
    }
    
    Wireable* topclk=nullptr;
    for (auto field : module->getType()->getRecord()) {
      if (isClockOrNestedClockType(field.second, this->clockType)) {
        topclk = def->sel("self")->sel(field.first);
      }
    }
    //Add clk if needed
    if (!topclk) {
      node.appendField("clk", this->clockType);
      topclk = def->sel("self")->sel("clk");
    }
    for (auto clk : clks) {
      this->connectClk(def, topclk, clk);
    }

    return true;
}
