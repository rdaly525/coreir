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

  // NOTE: Actually implement by checking types
  bool isBitVector(SimValue* v) {
    return true;
  }

  BitVec SimulatorState::getBitVec(CoreIR::Select* sel) {
    SimValue* v = getValue(sel);

    assert(isBitVector(v));

    return static_cast<BitVector*>(v)->getBits();
  }

  SimValue* SimulatorState::getValue(CoreIR::Select* sel) {
    auto it = valMap.find(sel);

    assert(it != std::end(valMap));

    return (*it).second;
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

  void SimulatorState::updateOrNode(const vdisc vd) {
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

    BitVec sum = s1->getBits() | s2->getBits();

    SimValue* oldVal = valMap[toSelect(outPair.second)];
    // Is this delete always safe?
    delete oldVal;

    valMap[toSelect(outPair.second)] = new BitVector(sum);
  }
  
  void SimulatorState::updateOutput(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Select* inst = toSelect(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 0);

    auto inConns = getInputConnections(vd, gr);

    assert(inConns.size() == 1);

    Conn inConn = *std::begin(inConns);
    InstanceValue arg = inConn.first;

    BitVector* s = static_cast<BitVector*>(valMap[arg.getWire()]);

    SimValue* oldVal = valMap[inst];
    delete oldVal;

    valMap[inst] = new BitVector(s->getBits());
    
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

    assert(isInstance(wd.getWire()));

    string opName = getOpName(*toInstance(wd.getWire()));
    if (opName == "and") {
      return updateAndNode(vd);
    } else if (opName == "or") {
      return updateOrNode(vd);
    }

    cout << "Unsupported node " << wd.getWire()->toString() << endl;
    assert(false);
  }

  void SimulatorState::execute() {
    for (auto& vd : topoOrder) {
      updateNodeValues(vd);
    }
  }

  void SimulatorState::setClock(CoreIR::Select* sel,
				const unsigned char clk_last,
				const unsigned char clk) {
  }
  
  SimulatorState::~SimulatorState() {
    for (auto& val : valMap) {
      delete val.second;
    }
  }

}
