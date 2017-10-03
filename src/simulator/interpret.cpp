#include "interpret.hpp"
#include "sim.hpp"

using namespace std;

namespace CoreIR {

  SimulatorState::SimulatorState(CoreIR::Module* mod) {
    buildOrderedGraph(mod, gr);
    topoOrder = topologicalSort(gr);
  }

  void SimulatorState::setValue(CoreIR::Select* sel, const BitVec& bv) {
    BitVector* b = new BitVector(bv);
    valMap[sel] = b;
  }

  BitVec SimulatorState::getValue(CoreIR::Select* sel) {
    return BitVec(32, 0);
  }

  void SimulatorState::updateAndNode(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, gr);

    assert(inConns.size() == 2);

    InstanceValue arg1 = findArg("in0", inConns);
    InstanceValue arg2 = findArg("in1", inConns);

    BitVector* s1 = static_cast<BitVector*>(valMap[arg1.getWire()]);
    BitVector* s2 = static_cast<BitVector*>(valMap[arg2.getWire()]);

    BitVec sum = s1->getBits() & s2->getBits();

    SimValue* oldVal = valMap[toSelect(outPair.second)];
    delete oldVal;

    valMap[toSelect(outPair.second)] = new BitVector(sum);
  }

  void SimulatorState::updateOutput(const vdisc vd) {
    
  }

  void SimulatorState::updateNodeValues(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    if (isGraphInput(wd)) {
      return;
    }

    if (isGraphOutput(wd)) {
      updateOutput(vd);
      return;
    }

    cout << "Unsupported node " << wd.getWire()->toString() << endl;
    
    assert(isInstance(wd.getWire()));
    
    if (getOpName(*toInstance(wd.getWire())) == "and") {
      return updateAndNode(vd);
    }

    cout << "Unsupported node " << wd.getWire()->toString() << endl;
    assert(false);
  }

  void SimulatorState::execute() {
    for (auto& vd : topoOrder) {
      updateNodeValues(vd);
    }
  }

  SimulatorState::~SimulatorState() {
    for (auto& val : valMap) {
      delete val.second;
    }
  }

}
