#include "coreir.h"
#include "coreir/passes/analysis/transform2combview.h"

using namespace std;
using namespace CoreIR;

struct Output {
  Wireable* output;
  set<Wireable*> states;
  set<Wireable*> inputs;
  Output(Wireable* output) : output(output) {}
}

void Passes::CreateCombView::setupCoreir(Module* m) {
  string mname = m->getName();
  if (mname == "reg" || mname == "regRst") {
    srcs[m].insert({"out"});
    snks[m].insert({"in"});
  }
  else if (mname == "mem") {
    for (auto record : m->getType()->getRecord()) {
      if (record.second->isInput()) {
        snks[m].insert({record.first});
      }
      else {
        assert(record.second->isOutput());
        srcs[m].insert({record.first});
      }
    }
  }
  else {
    set<SelectPath> inputs;
    set<SelectPath> outputs;
    for (auto record : m->getType()->getRecord()) {
      if (record.second->isInput()) {
        inputs.insert({record.first});
      }
      else {
        assert(record.second->isOutput());
        outputs.insert({record.first});
      }
    }
    combs.emplace(m,{inputs,outputs});
  }
}

string Passes::CreateCombView::ID = "createcombview";
bool Passes::CreateCombView::runOnInstanceGraphNode(InstanceGraphNode& node) {
  Module* m = node.getModule();
  if (m->getNamespace()->getName() == "coreir") {
    //Set srcs/snks/comb for coreir
    setupCoreir(m);
    return false;
  }
  if (m->getNamespace()->getName() == "corebit") {
    ASSERT(0,"NYI");
  }

  DirectedModule dm(m);

  set<Output> outputs;
  for (auto outcon : dm.getOutputs()) {
    Wireable* output = outcon.getSnkWireable();
    assert(output->getType()->isOutput());
    traverse(output,output)
  }


}

traverse(Wireable* cur, Wireable* out) {
  //get the connected wireable

}
