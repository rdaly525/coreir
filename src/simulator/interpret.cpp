#include "interpret.hpp"

#include "sim.hpp"

using namespace std;

namespace CoreIR {

  string getQualifiedOpName(CoreIR::Instance& inst) {
    string opName = inst.getModuleRef()->getNamespace()->getName() + "." +
      getOpName(inst);

    return opName;
  }

  void SimMemory::setAddr(const BitVec& bv, const BitVec& val) {
    assert(bv.bitLength() == log2(depth));
    assert(val.bitLength() == ((int) width));

    values.erase(bv);
    values.insert({bv, val});
  }

  BitVec SimMemory::getAddr(const BitVec& bv) const {

    assert(bv.bitLength() == log2(depth));

    auto it = values.find(bv);

    
    if (it == std::end(values)) {
      //cout << "Could not find " << bv << endl;
      return BitVec(width, 0);
    }

    return it->second;
  }
  
  ClockValue* toClock(SimValue* val) {
    assert(val->getType() == SIM_VALUE_CLK);

    return static_cast<ClockValue*>(val);
  }

  bool SimulatorState::rewind(const int halfCycles) {
    int newStateIndex = stateIndex - halfCycles;
    if (newStateIndex >= 0) {
      stateIndex = newStateIndex;
      return true;
    }

    return false;
  }

  void SimulatorState::setRegisterDefaults() {

    for (auto& vd : gr.getVerts()) {
      WireNode wd = gr.getNode(vd);

      if (isRegisterInstance(wd.getWire())) {
        Instance* inst = toInstance(wd.getWire());

        Values args = inst->getGenArgs();

        auto wArg = args["width"];

        assert(wArg != nullptr);

        uint width = (args["width"])->get<int>();

        // Set memory output port to default
        //setValue(inst->sel("out"), makeSimBitVector(BitVec(width, 0)));
        setRegister(inst->toString(), BitVec(width, 0));
        setValue(inst->sel("out"), getRegister(inst->toString()));
        
      }
    }

  }

  SimBitVector* SimulatorState::makeSimBitVector(const BitVector& bv) {
    auto sbv  = new SimBitVector(bv);
    allocatedValues.insert(sbv);

    return sbv;
  }

  std::vector<CircuitState>
  SimulatorState::getCircStates() const {
    return circStates;
  }

  int
  SimulatorState::numCircStates() const {
    return circStates.size();
  }
  
  int SimulatorState::getStateIndex() const {
    return stateIndex;
  }

  void SimulatorState::setLinebufferMemDefaults() {
    for (auto& vd : gr.getVerts()) {
      WireNode wd = gr.getNode(vd);

      if (isLinebufferMemInstance(wd.getWire())) {
        Instance* inst = toInstance(wd.getWire());

        Values args = inst->getGenArgs();
        uint width = (args["width"])->get<int>();
        uint depth = (args["depth"])->get<int>();

        // Set memory state to default value
        LinebufferMemory freshMem(width, depth);
        circStates[stateIndex].lbMemories.erase(inst->toString()); //, freshMem});
        circStates[stateIndex].lbMemories.insert({inst->toString(), freshMem});

        // Set memory output port to default
        setValue(inst->sel("rdata"), makeSimBitVector(BitVec(width, 0)));
        setValue(inst->sel("valid"), makeSimBitVector(BitVec(1, 0)));
      }
    }

  }

  void SimulatorState::setMemoryDefaults() {

    for (auto& vd : gr.getVerts()) {
      WireNode wd = gr.getNode(vd);

      if (isMemoryInstance(wd.getWire())) {
        Instance* inst = toInstance(wd.getWire());

        Values args = inst->getGenArgs();
        uint width = (args["width"])->get<int>();
        uint depth = (args["depth"])->get<int>();
        

        // Set memory state to default value
        SimMemory freshMem(width, depth);
        circStates[stateIndex].memories.insert({inst->toString(), freshMem});

        // Set memory output port to default
        setValue(inst->sel("rdata"), makeSimBitVector(BitVec(width, 0)));
        
      }
    }
  }

  void SimulatorState::setConstantDefaults() {

    // Set constants
    for (auto& vd : gr.getVerts()) {
      WireNode wd = gr.getNode(vd);

      if (isInstance(wd.getWire())) {

        Instance* inst = toInstance(wd.getWire());

        assert(inst != nullptr);

        string opName = inst->getModuleRef()->getNamespace()->getName() + "." + getOpName(*inst);

        cout << "opName = " << opName << endl;

        if ((opName == "coreir.const")) {
          bool foundValue = false;

          cout << "Found coreir const node " << inst->toString() << endl;

          int argInt = 0;
          for (auto& arg : inst->getModArgs()) {
            if (arg.first == "value") {
              foundValue = true;
              Value* valArg = arg.second; //.get();

              
              BitVector bv = valArg->get<BitVector>();
              argInt = bv.as_native_uint32();

            }
          }

          assert(foundValue);


          auto outSelects = getOutputSelects(inst);

          assert(outSelects.size() == 1);

          pair<string, Wireable*> outPair = *std::begin(outSelects);

          Select* outSel = toSelect(outPair.second);
          ArrayType& arrTp = toArray(*(outSel->getType()));
          
          setValue(outSel, makeSimBitVector(BitVec(arrTp.getLen(), argInt)));
        } else if (opName == "corebit.const") {

          bool foundValue = false;

          bool argInt = false;
          for (auto& arg : inst->getModArgs()) {
            if (arg.first == "value") {
              foundValue = true;
              Value* valArg = arg.second; //.get();

              bool bv = valArg->get<bool>();
              argInt = bv;

            }
          }

          assert(foundValue);


          auto outSelects = getOutputSelects(inst);

          assert(outSelects.size() == 1);

          pair<string, Wireable*> outPair = *std::begin(outSelects);

          Select* outSel = toSelect(outPair.second);
          
          setValue(outSel, makeSimBitVector(BitVec(1, argInt == 0 ? false : true)));

        }
      }
    }

  }

  void SimulatorState::setMainClock(const std::string& val) {
    Select* s = findSelect(val);
    mainClock = s;
  }

  void SimulatorState::setWatchPoint(const std::string& val,
                                     const BitVec& bv) {

    StopFunction func =
      [this, val, bv]() {

      if (isSet(val)) {
        if (getBitVec(val) == bv) {
          return true;
        }
      }
      return false;
    };

    stopConditions.push_back({val, func});
  }

  void SimulatorState::deleteWatchPoint(const std::string& name) {
    delete_if(stopConditions, [name](const StopCondition& sc) {
        return sc.name == name;
      });
  }

  bool SimulatorState::exists(const std::string& selStr) const {
    ModuleDef* def = mod->getDef();
    Wireable* w = def->sel(selStr);

    if (w == nullptr) {
      return false;
    }

    return true;
  }

  std::string concatInlined(const std::vector<std::string>& str) {
    string final = "";

    if (str.size() == 1) {
      return str[0];
    }

    for (uint i = 0; i < str.size(); i++) {
      final += str[i];
      if (i != (str.size() - 1)) {
        final += "$";
      }
    }

    return final;
  }

  SimValue* SimulatorState::getValue(const std::vector<std::string>& str)  {
    string concatName = concatInlined(str);

    return getValue(concatName);
  }
  
  BitVec SimulatorState::getBitVec(const std::vector<std::string>& str)  {
    string concatName = concatInlined(str);

    return getBitVec(concatName);
  }

  bool SimulatorState::isSet(const std::string& selStr) const {
    Select* s = findSelect(selStr);

    if (!valMapContains(s)) {
      return false;
    }

    return true;
  }

  bool SimulatorState::isSet(CoreIR::Select* s) const {
    if (!valMapContains(s)) {
      return false;
    }

    return true;
  }

  bool SimulatorState::hitWatchPoint() const {
    for (auto& cond : stopConditions) {
      if (cond.stopTest()) {
        return true;
      }
    }

    return false;
  }

  void SimulatorState::stepClock(CoreIR::Select* clkSelect) {
    ClockValue* clkVal = toClock(getValue(clkSelect));
    clkVal->flip();
  }

  void SimulatorState::stepClock(const std::string& str) {
    stepClock(findSelect(str));
  }

  void SimulatorState::stepMainClock() {
    stepClock(mainClock);
  }

  void SimulatorState::run() {
    while (!hitWatchPoint()) {
      runHalfCycle();
    }
  }

  bool SimulatorState::atLastState() {
    return stateIndex == (numCircStates() - 1);
  }

  void SimulatorState::runHalfCycle() {
    if (!atLastState()) {
      stateIndex++;
    } else {
      execute();
      stepClock(mainClock);
    }
  }

  SimulatorState::SimulatorState(CoreIR::Module* mod_) :
    mod(mod_), mainClock(nullptr) {

    buildOrderedGraph(mod, gr);

    cout << "Built graph, topological sorting" << endl;

    //std::clock_t start, end;

    //start = std::clock();

    cout << "Nodes in graph" << endl;
    for (auto& vd : gr.getVerts()) {
      cout << vd << " = " << gr.getNode(vd).getWire()->toString() << endl;
    }
    cout << "done." << endl;
    
    topoOrder = topologicalSort(gr);

    cout << "Nodes in sort" << endl;
    for (auto& vd : topoOrder) {
      cout << vd << " = " << gr.getNode(vd).getWire()->toString() << endl;
    }
    cout << "done." << endl;

    //end = std::clock();

    // std::cout << "Done. Time to sort " << gr.getVerts().size() << " vertices  : " << (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms" << std::endl;

    // Set initial state of the circuit
    CircuitState init;
    circStates = {init};
    stateIndex = 0;

    setConstantDefaults();
    setMemoryDefaults();
    setLinebufferMemDefaults();
    setRegisterDefaults();
    setDFFDefaults();
    setInputDefaults();


  }

  void SimulatorState::setInputDefaults() {
    
  }

  void SimulatorState::setValue(const std::vector<std::string>& name,
                                const BitVec& bv) {
    setValue(concatInlined(name), bv);
  }

  void SimulatorState::setValue(CoreIR::Select* sel, const BitVec& bv) {
    if (!atLastState()) {
      circStates.resize(stateIndex + 1);
      stateIndex = circStates.size() - 1;
    }

    assert(atLastState());

    SimBitVector* b = makeSimBitVector(bv);    
    setValue(sel, b);
  }

  CoreIR::Select* SimulatorState::findSelect(const std::string& name) const {
    ModuleDef* def = mod->getDef();
    Wireable* w = def->sel(name);
    Select* s = toSelect(w);

    return s;
  }

  
  void SimulatorState::setValue(const std::string& name, const BitVec& bv) {
    ModuleDef* def = mod->getDef();
    Wireable* w = def->sel(name);
    Select* s = toSelect(w);

    setValue(s, bv);
  }

  // NOTE: Actually implement by checking types
  bool isSimBitVector(SimValue* v) {
    return true;
  }

  BitVec SimulatorState::getBitVec(const std::string& str) {
    ModuleDef* def = mod->getDef();
    Wireable* w = def->sel(str);
    Select* sel = toSelect(w);

    return getBitVec(sel);
  }

  SimValue* SimulatorState::getValue(const std::string& name)  {
    ModuleDef* def = mod->getDef();
    Wireable* w = def->sel(name);
    Select* sel = toSelect(w);

    return getValue(sel);
  }

  BitVec SimulatorState::getBitVec(CoreIR::Select* sel) {

    SimValue* v = getValue(sel);

    assert(v != nullptr);
    assert(isSimBitVector(v));

    return static_cast<SimBitVector*>(v)->getBits();
  }

  SimValue* SimulatorState::getValue(CoreIR::Select* sel) {
    if (arrayAccess(sel)) {

      SimBitVector* val =
        static_cast<SimBitVector*>(getValue(toSelect(sel->getParent())));

      int index = selectNum(sel);

      return makeSimBitVector(BitVec(1, (val->getBits()).get(index)));
    }

    auto it = circStates[stateIndex].valMap.find(sel);

    if (it == std::end(circStates[stateIndex].valMap)) {
      return nullptr;
    }

    return (*it).second;
  }

  void SimulatorState::updateSliceNode(const vdisc vd) {
    WireNode wd = gr.getNode(vd);
    Instance* inst = toInstance(wd.getWire());
    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);
    auto inConns = getInputConnections(vd, gr);

    assert(inConns.size() == 1);

    InstanceValue arg1 = findArg("in", inConns);
    SimBitVector* s1 = static_cast<SimBitVector*>(getValue(arg1.getWire()));
    
    assert(s1 != nullptr);

    Values args = inst->getGenArgs();
    uint lo = (args["lo"])->get<int>();
    uint hi = (args["hi"])->get<int>();

    assert((hi - lo) > 0);

    BitVec res(hi - lo, 1);
    BitVec sB = s1->getBits();
    for (uint i = lo; i < hi; i++) {
      res.set(i - lo, sB.get(i));
    }

    setValue(toSelect(outPair.second), makeSimBitVector(res));
  }

  void SimulatorState::updateAndrNode(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, gr);

    assert(inConns.size() == 1);

    InstanceValue arg1 = findArg("in", inConns);

    SimBitVector* s1 = static_cast<SimBitVector*>(getValue(arg1.getWire()));
    
    assert(s1 != nullptr);
    
    BitVec res(1, 1);
    BitVec sB = s1->getBits();
    for (int i = 0; i < sB.bitLength(); i++) {
      if (sB.get(i) != 1) {
        res = BitVec(1, 0);
        break;
      }
    }

    setValue(toSelect(outPair.second), makeSimBitVector(res));
  }

  void SimulatorState::updateBitVecUnop(const vdisc vd, BitVecUnop op) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, gr);

    assert(inConns.size() == 2);

    InstanceValue arg1 = findArg("in0", inConns);

    SimBitVector* s1 = static_cast<SimBitVector*>(getValue(arg1.getWire()));
    
    assert(s1 != nullptr);
    
    BitVec res = op(s1->getBits());

    setValue(toSelect(outPair.second), makeSimBitVector(res));

  }

  void SimulatorState::updateBitVecBinop(const vdisc vd, BitVecBinop op) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, gr);

    assert(inConns.size() == 2);

    InstanceValue arg1 = findArg("in0", inConns);
    InstanceValue arg2 = findArg("in1", inConns);

    SimBitVector* s1 = static_cast<SimBitVector*>(getValue(arg1.getWire()));
    SimBitVector* s2 = static_cast<SimBitVector*>(getValue(arg2.getWire()));
    
    assert(s1 != nullptr);
    assert(s2 != nullptr);

    BitVector bv1 = s1->getBits();
    BitVector bv2 = s2->getBits();
    
    BitVec res = op(bv1, bv2);

    setValue(toSelect(outPair.second), makeSimBitVector(res));
  }

  void SimulatorState::updateAndNode(const vdisc vd) {
    updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
        return l & r;
      });

  }

  void SimulatorState::updateEqNode(const vdisc vd) {
    updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
        if (l == r ) {
          return BitVec(1, 1);
        } else {
          return BitVec(1, 0);
        }
      });
    

  }

  void SimulatorState::updateNeqNode(const vdisc vd) {

    updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
        if (l != r) {
          return BitVec(1, 1);
        } else {
          return BitVec(1, 0);
        }
      });


  }
  
  void SimulatorState::updateConcatNode(const vdisc vd) {
    updateBitVecBinop(vd, [](const BitVec& s1Bits, const BitVec& s2Bits) {
        BitVec conc(s1Bits.bitLength() + s2Bits.bitLength());

        for (int i = 0; i < s1Bits.bitLength(); i++) {
          conc.set(i, s1Bits.get(i));
        }

        for (int i = 0; i < s2Bits.bitLength(); i++) {
          conc.set(i + s1Bits.bitLength(), s2Bits.get(i));
        }

        return conc;
      });


  }
  
  void SimulatorState::updateAddNode(const vdisc vd) {
    updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
        return add_general_width_bv(l, r);
      });
    
  }

  void SimulatorState::updateMuxNode(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, gr);

    if (inConns.size() != 3) {
      cout << "Mux does not have 3 inputs!" << endl;
      for (auto& inConn : inConns) {
        cout << inConn.first.getWire()->toString() << " --> " << inConn.second.getWire()->toString() << endl;
      }

      assert(inConns.size() == 3);
    }

    InstanceValue arg1 = findArg("in0", inConns);
    InstanceValue arg2 = findArg("in1", inConns);
    InstanceValue sel = findArg("sel", inConns);

    SimBitVector* s1 = static_cast<SimBitVector*>(getValue(arg1.getWire()));
    SimBitVector* s2 = static_cast<SimBitVector*>(getValue(arg2.getWire()));
    
    SimBitVector* selB = static_cast<SimBitVector*>(getValue(sel.getWire()));

    assert(s1 != nullptr);
    assert(s2 != nullptr);
    assert(selB != nullptr);

    
    BitVec sum(s1->getBits().bitLength());
    
    if (selB->getBits() == BitVec(1, 0)) {
      sum = s1->getBits();
    } else {
      sum = s2->getBits();
    }

    setValue(toSelect(outPair.second), makeSimBitVector(sum));

  }

  void SimulatorState::updateOrNode(const vdisc vd) {
    updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
        return l | r;
      });
    
  }
  
  void SimulatorState::updateOutput(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Select* inst = toSelect(wd.getWire());

    // Type& t = *(inst->getType());
    
    // if (isArray(t)) {
    //   ArrayType& arrTp = toArray(t);
    //   int arrLen = arrTp.getLen();
      
    //   cout << "Array output of length " << arrLen << "!" << endl;
    //   assert(false);
    // }
    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 0);

    auto inConns = getInputConnections(vd, gr);

    cout << "Output = " << inst->toString() << endl;
    cout << "# of inputs = " << inConns.size() << endl;
    //assert(inConns.size() == 1);

    for (auto& inConn : inConns) {
      //Conn inConn = *std::begin(inConns);
      InstanceValue arg = inConn.first;
      InstanceValue receiver = inConn.second;

      //cout << "Updating " << inst->toString() << " with value " << arg.getWire()->toString() << endl;
      SimBitVector* s = static_cast<SimBitVector*>(getValue(arg.getWire()));

      assert(s != nullptr);

      Select* receiverSel = toSelect(receiver.getWire());

      setValue(receiverSel, makeSimBitVector(s->getBits()));
    }
    
  }

  void SimulatorState::updateLUTNNode(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, gr);

    assert(inConns.size() == 1);

    InstanceValue arg1 = findArg("in", inConns);

    SimBitVector* s1 = static_cast<SimBitVector*>(getValue(arg1.getWire()));
    
    assert(s1 != nullptr);

    Values genArgs = inst->getGenArgs();

    int width = genArgs["N"]->get<int>();

    Values args = inst->getModArgs();

    BitVector vals = args["init"]->get<BitVector>();

    assert(vals.bitLength() == (1 << width));

    bv_uint64 i = get_shift_int(s1->getBits());
    unsigned char lutBit = vals.get(i);
    
    setValue(toSelect(outPair.second), makeSimBitVector(BitVector(1, lutBit)));
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

    //string opName = getOpName(*toInstance(wd.getWire()));
    string opName = getQualifiedOpName(*toInstance(wd.getWire()));

    if ((opName == "coreir.and") || (opName == "corebit.and")) {
      updateAndNode(vd);
    } else if (opName == "coreir.eq") {
      updateEqNode(vd);
    } else if (opName == "coreir.neq") {
      updateNeqNode(vd);
    } else if ((opName == "coreir.or") || (opName == "corebit.or")) {
      updateOrNode(vd);
    } else if ((opName == "coreir.xor") || (opName == "corebit.xor")) {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          return l ^ r;
      });
    } else if (opName == "coreir.not") {
      updateBitVecUnop(vd, [](const BitVec& r) {
          return ~r;
      });
    } else if (opName == "coreir.andr") {
      updateAndrNode(vd);
    } else if (opName == "coreir.add") {
      updateAddNode(vd);
    } else if (opName == "coreir.sub") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
        return sub_general_width_bv(l, r);
      });
    } else if (opName == "coreir.mul") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
        return mul_general_width_bv(l, r);
      });
    } else if ((opName == "coreir.const") || (opName == "corebit.const")) {
    } else if (opName == "corebit.term") {
    } else if ((opName == "coreir.reg") || (opName == "corebit.dff")) {
    } else if ((opName == "coreir.mem") || (opName == "commonlib.LinebufferMem")) {
    } else if (opName == "coreir.mux") {
      updateMuxNode(vd);
    } else if (opName == "coreir.slice") {
      updateSliceNode(vd);
    } else if (opName == "coreir.concat") {
      updateConcatNode(vd);
    } else if (opName == "coreir.lshr") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          return lshr(l, r);
        });
    } else if (opName == "coreir.ashr") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          return ashr(l, r);
        });
    } else if (opName == "coreir.shl") {
       updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
           return shl(l, r);
         });
    } else if (opName == "coreir.ult") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          if (l < r) {
            return BitVec(1, 1);
          } else {
            return BitVec(1, 0);
          }
        });
    } else if (opName == "coreir.ule") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          if ((l < r) || (l == r)) {
            return BitVec(1, 1);
          } else {
            return BitVec(1, 0);
          }
        });
    } else if (opName == "coreir.ugt") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          if (l > r) {
            return BitVec(1, 1);
          } else {
            return BitVec(1, 0);
          }
        });
      
    } else if (opName == "coreir.uge") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          if ((l > r) || (l == r)) {
            return BitVec(1, 1);
          } else {
            return BitVec(1, 0);
          }
        });
    } else if (opName == "coreir.smax") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          if (signed_gt(l, r) || (l == r)) {
            return l;
          } else {
            return r;
          }
        });
    } else if (opName == "coreir.smin") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          if (signed_gt(l, r) || (l == r)) {
            return r;
          } else {
            return l;
          }
        });
    } else if (opName == "coreir.sgt") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          if (signed_gt(l, r)) {
            return BitVec(1, 1);
          } else {
            return BitVec(1, 0);
          }
        });
    } else if (opName == "coreir.sge") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          if (signed_gte(l, r)) {
            return BitVec(1, 1);
          } else {
            return BitVec(1, 0);
          }
        });
    } else if (opName == "coreir.slt") {

      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          if (!signed_gte(l, r)) {
            return BitVec(1, 1);
          } else {
            return BitVec(1, 0);
          }
        });
    } else if (opName == "coreir.sle") {

      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
          if (!signed_gt(l, r)) {
            return BitVec(1, 1);
          } else {
            return BitVec(1, 0);
          }
        });
    } else if (opName == "commonlib.lutN") {
      updateLUTNNode(vd);
    } else {
      cout << "Unsupported node: " << wd.getWire()->toString() << " has operation name: " << opName << endl;
      assert(false);
    }

  }

  void SimulatorState::updateLinebufferMemOutput(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 2);

    Wireable* outPair = CoreIR::findSelect("rdata", outSelects);
    Wireable* vaidSel = CoreIR::findSelect("valid", outSelects);

    BitVec newRData = getLinebufferValue(inst->toString());

    setValue(toSelect(outPair), makeSimBitVector(newRData));

    BitVector bv(1, 0);
    if (lineBufferOutIsValid(inst->toString())) {
      bv = BitVector(1, 1);
    }
    setValue(toSelect(vaidSel), makeSimBitVector(bv));
  }

  bool SimulatorState::lineBufferOutIsValid(const std::string& memName) {
    LinebufferMemory& mem =
      (circStates[stateIndex].lbMemories.find(memName))->second;

    return mem.isValid();
  }

  BitVector SimulatorState::getLinebufferValue(const std::string& memName) {
    LinebufferMemory& mem =
      (circStates[stateIndex].lbMemories.find(memName))->second;

    return mem.peek();
  }

  void SimulatorState::updateMemoryOutput(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, gr);

    assert(inConns.size() == 1);

    InstanceValue raddrV = findArg("raddr", inConns);

    SimBitVector* raddr = static_cast<SimBitVector*>(getValue(raddrV.getWire()));

    assert(raddr != nullptr);

    BitVec raddrBits = raddr->getBits();

    BitVec newRData = getMemory(inst->toString(), raddrBits);

    setValue(toSelect(outPair.second), makeSimBitVector(newRData));
    
  }

  void SimulatorState::updateLinebufferMemValue(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto inConns = getInputConnections(vd, gr);

    if (inConns.size() != 3) {
      cout << inConns.size() << " inputs " << endl;
      for (auto& conn : inConns) {
        cout << conn.first.getWire()->toString() << " -> " <<
          conn.second.getWire()->toString() << endl;
      }
      assert(inConns.size() == 3);
    }

    InstanceValue wdataV = findArg("wdata", inConns);
    InstanceValue clkArg = findArg("clk", inConns);
    InstanceValue enArg = findArg("wen", inConns);

    SimBitVector* wdata = static_cast<SimBitVector*>(getValue(wdataV.getWire()));
    SimBitVector* wen = static_cast<SimBitVector*>(getValue(enArg.getWire()));
    ClockValue* clkVal = toClock(getValue(clkArg.getWire()));
    
    assert(wdata != nullptr);
    assert(wen != nullptr);
    assert(clkVal != nullptr);

    BitVec enBit = wen->getBits();

    if ((clkVal->lastValue() == 0) &&
        (clkVal->value() == 1) &&
        (enBit == BitVec(1, 1))) {

      
      setLineBufferMem(inst->toString(), wdata->getBits());

      //assert(getMemory(inst->toString(), waddrBits) == wdata->getBits());
    }
    
  }

  void SimulatorState::setDFFDefaults() {
    for (auto& vd : gr.getVerts()) {
      WireNode wd = gr.getNode(vd);

      if (isDFFInstance(wd.getWire())) {
        Instance* inst = toInstance(wd.getWire());

        Values args = inst->getModArgs();

        bool val = args["init"]->get<bool>();

        setRegister(inst->toString(), BitVec(1, val ? 1 : 0));
        setValue(inst->sel("out"), getRegister(inst->toString()));
      }
    }
  }

  void SimulatorState::updateDFFOutput(const vdisc vd) {
    //assert(false);
    updateRegisterOutput(vd);
  }

  void SimulatorState::updateDFFValue(const vdisc vd) {
    //assert(false);
    updateRegisterValue(vd);
  }
  
  void SimulatorState::updateRegisterOutput(const vdisc vd) {

    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    BitVec newRData = getRegister(inst->toString()); //getMemory(inst->toString(), raddrBits);

    setValue(toSelect(outPair.second), makeSimBitVector(newRData));
    
  }

  void SimulatorState::updateMemoryValue(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto inConns = getInputConnections(vd, gr);

    assert(inConns.size() == 4);

    InstanceValue waddrV = findArg("waddr", inConns);
    InstanceValue wdataV = findArg("wdata", inConns);
    InstanceValue clkArg = findArg("clk", inConns);
    InstanceValue enArg = findArg("wen", inConns);


    SimBitVector* waddr = static_cast<SimBitVector*>(getValue(waddrV.getWire()));
    SimBitVector* wdata = static_cast<SimBitVector*>(getValue(wdataV.getWire()));
    SimBitVector* wen = static_cast<SimBitVector*>(getValue(enArg.getWire()));
    ClockValue* clkVal = toClock(getValue(clkArg.getWire()));
    
    assert(waddr != nullptr);
    assert(wdata != nullptr);
    assert(wen != nullptr);
    assert(clkVal != nullptr);

    BitVec waddrBits = waddr->getBits();
    BitVec enBit = wen->getBits();

    if ((clkVal->lastValue() == 0) &&
        (clkVal->value() == 1) &&
        (enBit == BitVec(1, 1))) {

      setMemory(inst->toString(), waddrBits, wdata->getBits());

      assert(getMemory(inst->toString(), waddrBits) == wdata->getBits());
    }

  }

  BitVec SimulatorState::getMemory(const std::string& name,
                                   const BitVec& addr) {
    auto it = circStates[stateIndex].memories.find(name);

    assert(it != std::end(circStates[stateIndex].memories));

    return (it->second).getAddr(addr);
  }

  void SimulatorState::updateRegisterValue(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inConns = getInputConnections(vd, gr);

    assert(inConns.size() >= 2);

    InstanceValue arg1 = findArg("in", inConns);
    InstanceValue clkArg = findArg("clk", inConns);

    SimBitVector* s1 = static_cast<SimBitVector*>(getValue(arg1.getWire()));
    ClockValue* clkVal = toClock(getValue(clkArg.getWire()));
    
    assert(s1 != nullptr);
    assert(clkVal != nullptr);

    if ((clkVal->lastValue() == 0) &&
        (clkVal->value() == 1)) {

      if (inConns.size() == 2) {

        //cout << "Setting register " << inst->toString() << " to " << s1->getBits() << endl;        
        //setValue(toSelect(outPair.second), makeSimBitVector(s1->getBits()));
        setRegister(inst->toString(), s1->getBits());

        assert(getRegister(inst->toString()) == s1->getBits());

      } else {
        assert(inConns.size() == 3);

        InstanceValue enArg = findArg("en", inConns);   

        SimBitVector* enBit = static_cast<SimBitVector*>(getValue(enArg.getWire()));

        assert(enBit != nullptr);

        if (enBit->getBits() == BitVec(1, 1)) {

          //cout << "Setting register " << inst->toString() << " to " << s1->getBits() << endl;
          //setValue(toSelect(outPair.second), makeSimBitVector(s1->getBits()));
          setRegister(inst->toString(), s1->getBits());

          assert(getRegister(inst->toString()) == s1->getBits());
        }

      }
    }

  }

  std::vector<vdisc> SimulatorState::unsetInputs() {
    NGraph& opGraph = getCircuitGraph();
    vector<vdisc> unset;
    for (auto& vd : opGraph.getVerts()) {

      WireNode w = opGraph.getNode(vd);

      if (isGraphInput(w)) {

        Select* inSel = toSelect(w.getWire());

        if (!isSet(inSel)) { //toSelect(sel.second))) {
          cout << "Select " << inSel->toString() << " is not set" << " in " << w.getWire()->toString() << endl;
          unset.push_back(vd);
        }

      }

    }

    return unset;
  }

  void SimulatorState::execute() {
    assert(atLastState());

    //std::clock_t start, end;

    //start = clock();

    CircuitState next = circStates[stateIndex];
    circStates.push_back(next);
    stateIndex++;

    if (hasMainClock()) {
      ClockValue* clockCopy = new ClockValue(*toClock(getValue(mainClock)));
      allocatedValues.insert(clockCopy);
      setValue(mainClock, clockCopy);
    }

    vector<vdisc> unsetIns = unsetInputs();
    if (unsetIns.size() > 0) {
      cout << "Cannot execute because " << unsetIns.size() << " input(s) are not set:" << endl;
      for (auto& vd : unsetIns) {
        cout << "\t" << getCircuitGraph().getNode(vd).getWire()->toString() << endl;
      }
      return;
    }

    //end = clock();

    // std::cout << "Done. Time to create next state = "
    //        << (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms"
    //        << std::endl;
    

    // start = clock();

    // Update sequential element outputs
    for (auto& vd : topoOrder) {
      WireNode wd = gr.getNode(vd);

      if (isMemoryInstance(wd.getWire()) && !wd.isReceiver) {
        // Does this work when the raddr port is not yet defined?
        updateMemoryOutput(vd);
      }

      if (isLinebufferMemInstance(wd.getWire()) && !wd.isReceiver) {
        // Does this work when the raddr port is not yet defined?
        updateLinebufferMemOutput(vd);
      }

      if (isRegisterInstance(wd.getWire()) && !wd.isReceiver) {
        updateRegisterOutput(vd);
      }

      if (isDFFInstance(wd.getWire()) && !wd.isReceiver) {
        updateDFFOutput(vd);
      }
      
    }

    //end = clock();

    // std::cout << "Done. Time to update memory outputs = "
    //        << (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms"
    //        << std::endl;

    // start = clock();

    // Update combinational node values
    for (auto& vd : topoOrder) {
      updateNodeValues(vd);
    }

    //end = clock();

    // std::cout << "Done. Time to update combinational nodes = "
    //        << (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms"
    //        << std::endl;

    // start = clock();

    // Update circuit state
    for (auto& vd : topoOrder) {
      WireNode wd = gr.getNode(vd);
      if (isRegisterInstance(wd.getWire()) && wd.isReceiver) {
        updateRegisterValue(vd);
      }

      // TODO: Source-Sink split LinebufferMem's
      if (isLinebufferMemInstance(wd.getWire())) {
        updateLinebufferMemValue(vd);
      }

      if (isMemoryInstance(wd.getWire())) {
        if (wd.isReceiver) {
          updateMemoryValue(vd);
        }
      }

      if (isDFFInstance(wd.getWire()) && wd.isReceiver) {
        updateDFFValue(vd);
      }
      
    }

    // end = clock();

    // std::cout << "Done. Time to update memory values = "
    //        << (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms"
    //        << std::endl;

  }

  void SimulatorState::setClock(const std::string& name,
                                const unsigned char clk_last,
                                const unsigned char clk) {

    ModuleDef* def = mod->getDef();
    Wireable* w = def->sel(name);
    Select* s = toSelect(w);

    setClock(s, clk_last, clk);

  }
  
  void SimulatorState::setClock(CoreIR::Select* sel,
                                const unsigned char clkLast,
                                const unsigned char clk) {
    auto clkVal = new ClockValue(clkLast, clk);
    allocatedValues.insert(clkVal);
    circStates[stateIndex].valMap[sel] = clkVal;
  }

  void SimulatorState::setLineBufferMem(const std::string& name,
                                        const BitVector& data) {
    LinebufferMemory& mem = (circStates[stateIndex].lbMemories.find(name))->second;
    mem.push(data);
  }

  void SimulatorState::setRegister(const std::string& name,
                                   const BitVec& data) {

    CircuitState& lastState = circStates[stateIndex];

    lastState.registers.erase(name);
    lastState.registers.insert({name, data});

  }

  BitVec SimulatorState::getRegister(const std::string& name) {
    return map_find(name, circStates[stateIndex].registers);
  }

  void SimulatorState::setMemory(const std::string& name,
                                 const BitVec& addr,
                                 const BitVec& data) {

    SimMemory& mem = (circStates[stateIndex].memories.find(name))->second;
    mem.setAddr(addr, data);

  }

  bool SimulatorState::valMapContains(CoreIR::Select* sel) const {
    return circStates[stateIndex].valMap.find(sel) != std::end(circStates[stateIndex].valMap);
  }

  void SimulatorState::setValue(CoreIR::Select* sel, SimValue* val) {
    if (arrayAccess(sel)) {

      assert(val->getType() == SIM_VALUE_BV);

      SimBitVector* bv = static_cast<SimBitVector*>(val);
      BitVector bits = bv->getBits();

      assert(bits.bitLength() == 1);
      
      Select* parent = toSelect(sel->getParent());
      int arrLen = arrayLen(parent);

      SimBitVector* val;
      if (isSet(parent)) {
        val = static_cast<SimBitVector*>(getValue(parent));
      } else {
        // TODO: Wrap allocations and delete at end of context
        val = makeSimBitVector(BitVector(arrLen));
      }

      BitVector oldBv = val->getBits();

      int index = selectNum(sel);
      oldBv.set(index, bits.get(0));

      circStates[stateIndex].valMap[parent] = makeSimBitVector(oldBv);

    }
    circStates[stateIndex].valMap[sel] = val;
  }
  
  SimulatorState::~SimulatorState() {
    for (auto& val : allocatedValues) {
      delete val;
    }
  }

}
