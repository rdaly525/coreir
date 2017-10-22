#include "interpret.hpp"

#include "sim.hpp"

using namespace std;

namespace CoreIR {

  void SimMemory::setAddr(const BitVec& bv, const BitVec& val) {
    assert(bv.bitLength() == log2(depth));
    assert(val.bitLength() == width);

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
	setValue(inst->sel("out"), makeSimBitVector(BitVec(width, 0)));
	
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

	string opName = getOpName(*inst);

	if ((opName == "const")) {
	  bool foundValue = false;

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
	} else if (opName == "bitconst") {

	  bool foundValue = false;

	  int argInt = 0;
	  for (auto& arg : inst->getModArgs()) {
	    if (arg.first == "value") {
	      foundValue = true;
	      Value* valArg = arg.second; //.get();

	      int bv = valArg->get<int>();
	      argInt = bv;

	    }
	  }

	  assert(foundValue);


	  auto outSelects = getOutputSelects(inst);

	  assert(outSelects.size() == 1);

	  pair<string, Wireable*> outPair = *std::begin(outSelects);

	  Select* outSel = toSelect(outPair.second);
	  
	  setValue(outSel, makeSimBitVector(BitVec(1, argInt)));

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

    for (int i = 0; i < str.size(); i++) {
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

    topoOrder = topologicalSort(gr);

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
    for (int i = lo; i < hi; i++) {
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

    assert(inConns.size() == 3);

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

    string opName = getOpName(*toInstance(wd.getWire()));
    if ((opName == "and") || (opName == "bitand")) {
      updateAndNode(vd);
    } else if (opName == "eq") {
      updateEqNode(vd);
    } else if (opName == "neq") {
      updateNeqNode(vd);
    } else if ((opName == "or") || (opName == "bitor")) {
      updateOrNode(vd);
    } else if ((opName == "xor") || (opName == "bitxor")) {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  return l ^ r;
      });
    } else if (opName == "not") {
      updateBitVecUnop(vd, [](const BitVec& r) {
	  return ~r;
      });
    } else if (opName == "andr") {
      updateAndrNode(vd);
    } else if (opName == "add") {
      updateAddNode(vd);
    } else if (opName == "sub") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	return sub_general_width_bv(l, r);
      });
    } else if (opName == "mul") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	return mul_general_width_bv(l, r);
      });
    } else if ((opName == "const") || (opName == "bitconst")) {
    } else if (opName == "bitterm") {
    } else if (opName == "reg") {
    } else if ((opName == "mem") || (opName == "LinebufferMem")) {
    } else if (opName == "mux") {
      updateMuxNode(vd);
    } else if (opName == "slice") {
      updateSliceNode(vd);
    } else if (opName == "concat") {
      updateConcatNode(vd);
    } else if (opName == "lshr") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  return lshr(l, r);
	});
    } else if (opName == "ashr") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  return ashr(l, r);
	});
    } else if (opName == "shl") {
       updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	   return shl(l, r);
	 });
    } else if (opName == "ult") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  if (l < r) {
	    return BitVec(1, 1);
	  } else {
	    return BitVec(1, 0);
	  }
	});
    } else if (opName == "ule") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  if ((l < r) || (l == r)) {
	    return BitVec(1, 1);
	  } else {
	    return BitVec(1, 0);
	  }
	});
    } else if (opName == "ugt") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  if (l > r) {
	    return BitVec(1, 1);
	  } else {
	    return BitVec(1, 0);
	  }
	});
      
    } else if (opName == "uge") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  if ((l > r) || (l == r)) {
	    return BitVec(1, 1);
	  } else {
	    return BitVec(1, 0);
	  }
	});
    } else if (opName == "smax") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  if (signed_gt(l, r) || (l == r)) {
	    return l;
	  } else {
	    return r;
	  }
	});
    } else if (opName == "smin") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  if (signed_gt(l, r) || (l == r)) {
	    return r;
	  } else {
	    return l;
	  }
	});
    } else if (opName == "sgt") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  if (signed_gt(l, r)) {
	    return BitVec(1, 1);
	  } else {
	    return BitVec(1, 0);
	  }
	});
    } else if (opName == "sge") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  if (signed_gte(l, r)) {
	    return BitVec(1, 1);
	  } else {
	    return BitVec(1, 0);
	  }
	});
    } else if (opName == "slt") {

      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  if (!signed_gte(l, r)) {
	    return BitVec(1, 1);
	  } else {
	    return BitVec(1, 0);
	  }
	});
    } else if (opName == "sle") {

      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
	  if (!signed_gt(l, r)) {
	    return BitVec(1, 1);
	  } else {
	    return BitVec(1, 0);
	  }
	});
    } else if (opName == "lutN") {
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

	setValue(toSelect(outPair.second), makeSimBitVector(s1->getBits()));
      } else {
	assert(inConns.size() == 3);

	InstanceValue enArg = findArg("en", inConns);	

	SimBitVector* enBit = static_cast<SimBitVector*>(getValue(enArg.getWire()));

	assert(enBit != nullptr);

	if (enBit->getBits() == BitVec(1, 1)) {

	  setValue(toSelect(outPair.second), makeSimBitVector(s1->getBits()));
	}

      }
    }

  }

  void SimulatorState::execute() {
    assert(atLastState());

    //std::clock_t start, end;

    //start = clock();

    CircuitState next = circStates[stateIndex];

    circStates.push_back(next);
    stateIndex++;

    //end = clock();

    // std::cout << "Done. Time to create next state = "
    // 	      << (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms"
    // 	      << std::endl;
    

    // start = clock();

    // Update memory outputs
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
      
    }

    //end = clock();

    // std::cout << "Done. Time to update memory outputs = "
    // 	      << (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms"
    // 	      << std::endl;

    // start = clock();

    // Update combinational node values
    for (auto& vd : topoOrder) {
      updateNodeValues(vd);
    }

    //end = clock();

    // std::cout << "Done. Time to update combinational nodes = "
    // 	      << (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms"
    // 	      << std::endl;

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

    }

    // end = clock();

    // std::cout << "Done. Time to update memory values = "
    // 	      << (end - start) / (double)(CLOCKS_PER_SEC / 1000) << " ms"
    // 	      << std::endl;

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
      cout << "Array access " << sel->toString() << endl;

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

      cout << "Array access to " << sel->getSelStr() << "!" << endl;

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
