#include "coreir/simulator/interpreter.h"
#include "coreir/simulator/simulator.h"

using namespace std;

namespace CoreIR {

  int bitsToIndex(const int depth) {
    return ceil(log2(depth)) + 1;
  }

  void SimMemory::setAddr(const BitVec& addr, const BitVec& val) {

    assert(val.bitLength() == ((int) width));
    // Cannot access out of range elements
    assert(addr.to_type<uint>() < depth);

    values.erase(addr);
    values.insert({addr, val});
  }

  BitVec SimMemory::getAddr(const BitVec& bv) const {
    // cout << "bv.bitLength() = " << bv.bitLength() << endl;
    // cout << "log2(depth))   = " << log2(depth) << endl;

    //assert(bv.bitLength() == bitsToIndex(depth)); //log2(depth));

    // Cannot access out of range elements
    assert(bv.to_type<uint>() < depth);

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

        Values args = inst->getModuleRef()->getGenArgs();

        auto wArg = args["width"];

        assert(wArg != nullptr);

        int width = (args["width"])->get<int>();
        BitVector initVal = inst->getModArgs().at("init")->get<BitVector>();

        assert(initVal.bitLength() == width);

        // Set memory output port to default
        setRegister(inst->toString(), initVal);
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

  void SimulatorState::setMemoryDefaults() {

    for (auto& vd : gr.getVerts()) {
      WireNode wd = gr.getNode(vd);

      if (isMemoryInstance(wd.getWire())) {
        Instance* inst = toInstance(wd.getWire());

        Values args = inst->getModuleRef()->getGenArgs();
        uint width = (args["width"])->get<int>();
        uint depth = (args["depth"])->get<int>();
        

        // Set memory state to default value
        SimMemory freshMem(width, depth);
        circStates[stateIndex].memories.insert({inst->toString(), freshMem});

        // Set memory output port to default
        setValue(inst->sel("rdata"), makeSimBitVector(BitVec(width, 0)));
        setValue(inst->sel("raddr"), makeSimBitVector(BitVec(ceil(log2(depth)), 0)));
      }
    }
  }

  void SimulatorState::setConstantDefaults() {

    for (auto& vd : gr.getVerts()) {
      WireNode wd = gr.getNode(vd);

      if (isInstance(wd.getWire())) {

        Instance* inst = toInstance(wd.getWire());

        assert(inst != nullptr);

        string opName = inst->getModuleRef()->getNamespace()->getName() + "." + getOpName(*inst);

        if ((opName == "coreir.const")) {

          BitVector argInt = inst->getModArgs().at("value")->get<BitVector>();

          Select* outSel = inst->sel("out");

          setValue(outSel, makeSimBitVector(argInt));
        } else if (opName == "corebit.const") {

          bool argInt = inst->getModArgs().at("value")->get<bool>();

          Select* outSel = inst->sel("out");
          setValue(outSel, makeSimBitVector(BitVec(1, argInt == 0 ? false : true)));

        }
      }
    }

  }

  void SimulatorState::setMainClock(const std::string& val) {
    Select* s = findSelect(val);
    setMainClock(s);

  }

  void SimulatorState::setMainClock(CoreIR::Select* s) {
    mainClock = s;
  }
  
  void SimulatorState::setMainClock(const std::vector<std::string>& path) {
    std::string name = concatInlined(path);
    setMainClock(name);
  }

  void SimulatorState::setWatchPoint(const std::string& val,
                                     const BitVec& bv) {

    StopFunction func =
      [this, val, bv]() {

      if (exists(val)) {

        if (isSet(val)) {
          SimValue* nm = getValue(val);

          if (nm != nullptr) {
            SimBitVector* simVal = toSimBitVector(nm);

            if (simVal->getBits() == bv) {
              return true;
            } else {
              return false;
            }
          }
        } else {
          return false;
        }
      }

      SimValue* res = getValueByOriginalName(val);
      if (res != nullptr) {
        SimBitVector* simVal = toSimBitVector(res);

        if (simVal->getBits() == bv) {
          return true;
        } else {
          return false;
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
    return def->canSel(selStr);
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

  std::string concatSelects(const std::vector<std::string>& str) {
    string final = "";

    if (str.size() == 1) {
      return str[0];
    }

    for (uint i = 0; i < str.size(); i++) {
      final += str[i];
      if (i != (str.size() - 1)) {
        final += ".";
      }
    }

    return final;
  }

  std::string concatSelects(const std::deque<std::string>& str) {
    string final = "";

    if (str.size() == 1) {
      return str[0];
    }

    for (uint i = 0; i < str.size(); i++) {
      final += str[i];
      if (i != (str.size() - 1)) {
        final += ".";
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

  void SimulatorState::setWatchPoint(const std::vector<std::string>& path, const BitVec& bv) {
    string concatName = concatInlined(path);

    return setWatchPoint(concatName, bv);
  }

  bool SimulatorState::isSet(const std::string& selStr) const {
    Select* s = findSelect(selStr);

    return isSet(s);
  }

  bool SimulatorState::isSet(CoreIR::Select* s) const {
    if (!valMapContains(s)) {

      string str = s->getSelStr();
      if (isNumber(str)) {
        return isSet(toSelect(s->getParent()));
      }

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

  void SimulatorState::runBack() {
    while (!hitWatchPoint()) {
      rewind(1);
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

  void SimulatorState::findMainClock() {
    auto clkInput = CoreIR::findMainClock(getCircuitGraph());

    if (clkInput != nullptr) {
      setMainClock(clkInput);
    }
  }

  SimulatorState::SimulatorState(CoreIR::Module* mod_) :
    mod(mod_), mainClock(nullptr) {

    assert(mod->hasDef());

    mod->getDef()->getContext()->runPasses({"verifyflattenedtypes"}, {mod->getNamespace()->getName(), "global"});
    hasSymTable = false;

    // Create symbol table if it exists
    if (mod->getMetaData().get<map<string,json>>().count("symtable")) {
      hasSymTable = true;
      symTable =
        mod->getMetaData()["symtable"].get<map<string,json>>();
    }

    buildOrderedGraph(mod, gr);

    deque<vdisc> order = topologicalSortNoFail(gr);

    // TODO: This test for combinational loops can fail for 2 element circuits,
    // replace it with something more robust
    if (order.size() == gr.getVerts().size()) {
      topoOrder = order;
      hasCombinationalLoop = false;
    } else {
      hasCombinationalLoop = true;
    }

    // Set initial state of the circuit
    CircuitState init;
    circStates = {init};
    stateIndex = 0;

    findMainClock();

    setConstantDefaults();
    setMemoryDefaults();
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

    ASSERT(def->canSel(name), name + " is not a port of the module being simulated");

    Wireable* w = def->sel(name);
    Select* s = toSelect(w);

    setValue(s, bv);
  }

  bool isSimBitVector(SimValue* v) {
    return v->getType() == SIM_VALUE_BV;
  }

  SimBitVector* toSimBitVector(SimValue* v) {
    assert(isSimBitVector(v));

    return static_cast<SimBitVector*>(v);
  }

  BitVec SimulatorState::getBitVec(const std::string& str) {
    ModuleDef* def = mod->getDef();
    Wireable* w = def->sel(str);
    Select* sel = toSelect(w);

    return getBitVec(sel);
  }

  SimValue* SimulatorState::getValue(const std::string& name)  {
    ModuleDef* def = mod->getDef();

    if (def->canSel(name)) {
      Wireable* w = def->sel(name);
      Select* sel = toSelect(w);

      return getValue(sel);
    }

    return nullptr;
  }

  BitVec SimulatorState::getBitVec(CoreIR::Select* sel) {
    SimValue* v = getValue(sel);

    ASSERT(v != nullptr, sel->toString() + " cannot be found");

    return toSimBitVector(v)->getBits();
  }

  SimValue* SimulatorState::getValue(CoreIR::Select* sel) {
    if (arrayAccess(sel)) {

      SimBitVector* val =
        static_cast<SimBitVector*>(getValue(toSelect(sel->getParent())));

      assert(val != nullptr);

      int index = selectNum(sel);

      BitVec bv(1, 0);
      bv.set(0, val->getBits().get(index));

      return makeSimBitVector(bv);
    }

    assert(mod->getDef()->canSel(sel->toString()));

    auto it = circStates[stateIndex].valMap.find(sel);

    if (it == std::end(circStates[stateIndex].valMap)) {
      return nullptr;
    }

    return (*it).second;
  }

  void SimulatorState::updateSliceNode(const vdisc vd) {
    WireNode wd = gr.getNode(vd);
    Instance* inst = toInstance(wd.getWire());
    //auto outSelects = getOutputSelects(inst);

    updateInputs(vd);

    //assert(outSelects.size() == 1);

    //pair<string, Wireable*> outPair = *std::begin(outSelects);
    //auto inConns = getInputConnections(vd, gr);

    //assert(inConns.size() == 1);

    Select* argSel = inst->sel("in");
    ASSERT(isSet(argSel), "in must have a value to evaluate this node");
    SimBitVector* s1 = static_cast<SimBitVector*>(getValue(argSel));
    
    // InstanceValue arg1 = findArg("in", inConns);
    // SimBitVector* s1 = static_cast<SimBitVector*>(getValue(arg1.getWire()));
    
    assert(s1 != nullptr);

    Values args = inst->getModuleRef()->getGenArgs();
    uint lo = (args["lo"])->get<int>();
    uint hi = (args["hi"])->get<int>();

    assert((hi - lo) > 0);

    BitVec res(hi - lo, 1);
    BitVec sB = s1->getBits();
    for (uint i = lo; i < hi; i++) {
      res.set(i - lo, sB.get(i));
    }

    //setValue(toSelect(outPair.second), makeSimBitVector(res));
    setValue(toSelect(inst->sel("out")), makeSimBitVector(res));
  }

  void SimulatorState::updateAndrNode(const vdisc vd) {

    updateInputs(vd);

    WireNode wd = gr.getNode(vd);
    Instance* inst = toInstance(wd.getWire());

    Select* inSel = inst->sel("in");

    ASSERT(isSet(inSel), "in must have a value to evaluate this node");

    SimBitVector* s1 = static_cast<SimBitVector*>(getValue(inSel));
    
    assert(s1 != nullptr);
    
    BitVec res(1, 1);
    BitVec sB = s1->getBits();
    for (int i = 0; i < sB.bitLength(); i++) {
      if (sB.get(i) != 1) {
        res = BitVec(1, 0);
        break;
      }
    }

    Select* outSel = inst->sel("out");
    setValue(outSel, makeSimBitVector(res));
  }

  void SimulatorState::updateOrrNode(const vdisc vd) {
    updateInputs(vd);

    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    Select* inSel = inst->sel("in");

    ASSERT(isSet(inSel), "in must have a value to evaluate this node");

    SimBitVector* s1 = static_cast<SimBitVector*>(getValue(inSel));
    
    assert(s1 != nullptr);
    
    BitVec res(1, 0);
    BitVec sB = s1->getBits();
    for (int i = 0; i < sB.bitLength(); i++) {
      if (sB.get(i) == 1) {
        res = BitVec(1, 1);
        break;
      }
    }

    setValue(toSelect(outPair.second), makeSimBitVector(res));
  }
  
  void SimulatorState::updateBitVecUnop(const vdisc vd, BitVecUnop op) {
    updateInputs(vd);

    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    Select* outSel = inst->sel("out");

    Select* arg1 = inst->sel("in");
    BitVector bv1 = getBitVec(arg1);
    
    BitVec res = op(bv1);

    setValue(outSel, makeSimBitVector(res));

  }

  void SimulatorState::updateInputs(const vdisc vd) {
    auto inConns = getInputConnections(vd, gr);
    for (auto& conn : inConns) {
      Select* source = toSelect(conn.first.getWire());
      Select* dest = toSelect(conn.second.getWire());

      setValue(dest, getValue(source));

    }

  }

  void SimulatorState::updateBitVecBinop(const vdisc vd, BitVecBinop op) {

    updateInputs(vd);

    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    Select* arg1 = inst->sel("in0");
    BitVector bv1 = getBitVec(arg1);
    
    Select* arg2 = inst->sel("in1");
    BitVector bv2 = getBitVec(arg2);

    BitVec res = op(bv1, bv2);

    setValue(toSelect(inst->sel("out")), makeSimBitVector(res));
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
    updateBitVecBinop(vd, [](const BitVec& s0Bits, const BitVec& s1Bits) {
        BitVec conc(s0Bits.bitLength() + s1Bits.bitLength());

        for (int i = 0; i < s0Bits.bitLength(); i++) {
          conc.set(i, s0Bits.get(i));
        }

        for (int i = 0; i < s1Bits.bitLength(); i++) {
          conc.set(i + s0Bits.bitLength(), s1Bits.get(i));
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
    updateInputs(vd);

    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    Select* arg1 = inst->sel("in0");
    BitVector bv1 = getBitVec(arg1);
    
    Select* arg2 = inst->sel("in1");
    BitVector bv2 = getBitVec(arg2);

    Select* sel = inst->sel("sel");
    BitVector selB = getBitVec(sel);
    
    BitVec sum(bv1.bitLength());
    
    if (selB == BitVec(1, 0)) {
      sum = bv1;
    } else {
      sum = bv2;
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

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 0);

    auto inConns = getInputConnections(vd, gr);

    for (auto& inConn : inConns) {

      InstanceValue arg = inConn.first;
      InstanceValue receiver = inConn.second;

      SimBitVector* s = static_cast<SimBitVector*>(getValue(arg.getWire()));

      assert(s != nullptr);

      Select* receiverSel = toSelect(receiver.getWire());

      setValue(receiverSel, makeSimBitVector(s->getBits()));
    }
    
  }

  void SimulatorState::updateZextNode(const vdisc vd) {
    updateInputs(vd);

    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    uint inWidth = inst->getModuleRef()->getGenArgs().at("width_in")->get<int>();
    uint outWidth = inst->getModuleRef()->getGenArgs().at("width_out")->get<int>();
    
    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inSels = getInputSelects(inst);
    assert(inSels.size() == 1);
    
    Select* arg1 = toSelect(CoreIR::findSelect("in", inSels));
    BitVector bv1 = getBitVec(arg1); //s1->getBits();

    ASSERT(((uint) bv1.bitLength()) == inWidth, "bit vector argument to coreir.zext has wrong input width");

    BitVec res(outWidth, 0);
    for (uint i = 0; i < inWidth; i++) {
      res.set(i, bv1.get(i));
    }

    setValue(toSelect(outPair.second), makeSimBitVector(res));

  }

  void SimulatorState::updateLUTNNode(const vdisc vd) {

    updateInputs(vd);

    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    auto outSelects = getOutputSelects(inst);

    assert(outSelects.size() == 1);

    pair<string, Wireable*> outPair = *std::begin(outSelects);

    auto inSels = getInputSelects(inst);
    assert(inSels.size() == 1);
    
    Select* arg1 = toSelect(CoreIR::findSelect("in", inSels));
    BitVector bv1 = getBitVec(arg1); //s1->getBits();
    
    Values genArgs = inst->getModuleRef()->getGenArgs();

    int width = genArgs["N"]->get<int>();

    Values args = inst->getModArgs();

    BitVector vals = args["init"]->get<BitVector>();

    assert(vals.bitLength() == (1 << width));

    bv_uint64 i = get_shift_int(bv1); //get_shift_int(s1->getBits());
    unsigned char lutBit = vals.get(i).binary_value();
    
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

    if (!(isInstance(wd.getWire()))) {
      cout << "Error in updateNodeValues " << wd.getWire()->toString() << endl;
    }
    assert(isInstance(wd.getWire()));

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
    } else if ((opName == "coreir.zext")) {
      updateZextNode(vd);
    } else if ((opName == "coreir.not") || (opName == "corebit.not")) {
      updateBitVecUnop(vd, [](const BitVec& r) {
          return ~r;
      });
    } else if (opName == "coreir.andr") {
      updateAndrNode(vd);
    } else if (opName == "coreir.orr") {
      updateOrrNode(vd);
    } else if (opName == "coreir.add") {
      updateAddNode(vd);
    } else if (opName == "coreir.neg") {
      updateBitVecUnop(vd, [](const BitVec& bv) {
          return negate_general_width_bv(bv);
        });
    } else if (opName == "coreir.sub") {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
        return sub_general_width_bv(l, r);
      });
    } else if ((opName == "coreir.mul")) {
      updateBitVecBinop(vd, [](const BitVec& l, const BitVec& r) {
        return mul_general_width_bv(l, r);
      });
    } else if ((opName == "coreir.const") || (opName == "corebit.const")) {
    } else if (opName == "corebit.term") {
    } else if ((opName == "coreir.reg") || (opName == "corebit.reg")) {
    } else if ((opName == "coreir.mem") || (opName == "memory.rowbuffer")) {
    } else if ((opName == "coreir.mux")  || (opName == "corebit.mux")) {
      updateMuxNode(vd);
    } else if ((opName == "coreir.wire") || (opName == "corebit.wire")) {
      updateBitVecUnop(vd, [](const BitVec& r) {
          return r;
      });
    } else if ((opName == "coreir.term") || (opName == "corebit.term")) {
      // No-op
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

  void SimulatorState::updateMemoryOutput(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    updateInputs(vd);

    Instance* inst = toInstance(wd.getWire());

    Select* arg1 = inst->sel("raddr");
    BitVector raddrBits = getBitVec(arg1);

    BitVec newRData = getMemory(inst->toString(), raddrBits);

    setValue(inst->sel("rdata"), makeSimBitVector(newRData));
    
  }

  void SimulatorState::setDFFDefaults() {
    for (auto& vd : gr.getVerts()) {
      WireNode wd = gr.getNode(vd);

      if (isDFFInstance(wd.getWire())) {
        Instance* inst = toInstance(wd.getWire());

        Values args = inst->getModArgs();
        cout << toString(inst) << endl;
        cout << toString(args) << endl;
        bool val = args["init"]->get<bool>();

        setRegister(inst->toString(), BitVec(1, val ? 1 : 0));
        setValue(inst->sel("out"), getRegister(inst->toString()));
      }
    }
  }

  void SimulatorState::updateDFFOutput(const vdisc vd) {
    updateRegisterOutput(vd);
  }

  void SimulatorState::updateDFFValue(const vdisc vd) {
    updateRegisterValue(vd);
  }
  
  void SimulatorState::updateRegisterOutput(const vdisc vd) {

    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    BitVec newRData = getRegister(inst->toString());

    setValue(inst->sel("out"), makeSimBitVector(newRData));
  }

  void SimulatorState::updateMemoryValue(const vdisc vd) {
    WireNode wd = gr.getNode(vd);

    Instance* inst = toInstance(wd.getWire());

    updateInputs(vd);

    // auto inConns = getInputConnections(vd, gr);

    // assert(inConns.size() == 4);

    // InstanceValue waddrV = findArg("waddr", inConns);
    // InstanceValue wdataV = findArg("wdata", inConns);
    // InstanceValue clkArg = findArg("clk", inConns);
    // InstanceValue enArg = findArg("wen", inConns);

    Select* waddrV = inst->sel("waddr");
    Select* wdataV = inst->sel("wdata");
    Select* clkArg = inst->sel("clk");
    Select* enArg = inst->sel("wen");
    

    // SimBitVector* waddr = static_cast<SimBitVector*>(getValue(waddrV.getWire()));
    // SimBitVector* wdata = static_cast<SimBitVector*>(getValue(wdataV.getWire()));
    // SimBitVector* wen = static_cast<SimBitVector*>(getValue(enArg.getWire()));
    // ClockValue* clkVal = toClock(getValue(clkArg.getWire()));

    SimBitVector* waddr = static_cast<SimBitVector*>(getValue(waddrV));
    SimBitVector* wdata = static_cast<SimBitVector*>(getValue(wdataV));
    SimBitVector* wen = static_cast<SimBitVector*>(getValue(enArg));
    ClockValue* clkVal = toClock(getValue(clkArg));
    
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

      //assert(getMemory(inst->toString(), waddrBits) == wdata->getBits());
      assert(same_representation(getMemory(inst->toString(), waddrBits), wdata->getBits()));
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

    // New code
    updateInputs(vd);

    auto inSels = getInputSelects(inst);
    ASSERT(inSels.size() == 2, to_string(inSels.size()) + " inSels" + toString(inst));

    Select* arg1 = toSelect(CoreIR::findSelect("in", inSels));
    SimBitVector* s1 =
      static_cast<SimBitVector*>(getValue(arg1));

    BitVector bv1(0);
    if (s1 != nullptr) {
      bv1 = s1->getBits();
    } else {
      int width = (inst->getModuleRef()->getGenArgs())["width"]->get<int>();
      // Set dummy value for initilization
      bv1 = BitVector(width, 0);
    }
    
    //auto inConns = getInputConnections(vd, gr);

    //assert(inSels.size() >= 2);

    //InstanceValue clkArg = findArg("clk", inConns);
    Select* clkArg = inst->sel("clk");
    //ClockValue* clkVal = toClock(getValue(clkArg.getWire()));
    ClockValue* clkVal = toClock(getValue(clkArg));
    
    assert(clkVal != nullptr);

    if ((clkVal->lastValue() == 0) &&
        (clkVal->value() == 1)) {

      if (inSels.size() == 2) {

        setRegister(inst->toString(), bv1); //s1->getBits());
        ASSERT(same_representation(getRegister(inst->toString()),bv1),inst->toString() + " != " + toString(bv1)); //s1->getBits());

      } else {
        assert(inSels.size() == 3);

        //InstanceValue enArg = findArg("en", inConns);
        Select* enArg = inst->sel("en");
        //SimBitVector* enBit = static_cast<SimBitVector*>(getValue(enArg.getWire()));
        SimBitVector* enBit = static_cast<SimBitVector*>(getValue(enArg));

        assert(enBit != nullptr);

        if (enBit->getBits() == BitVec(1, 1)) {

          setRegister(inst->toString(), bv1);

          assert(same_representation(getRegister(inst->toString()), bv1));
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
          //cout << "Select " << inSel->toString() << " is not set" << " in " << w.getWire()->toString() << endl;
          unset.push_back(vd);
        }

      }

    }

    return unset;
  }

  void SimulatorState::resetCircuit() {
    exeCombinational();
  }

  void SimulatorState::exeSequential() {

    for (auto& vd : gr.getVerts()) {
      WireNode wd = gr.getNode(vd);
      if (isRegisterInstance(wd.getWire()) && wd.isReceiver) {

        updateRegisterValue(vd);
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

  }

  void SimulatorState::exeCombinational() {
    for (uint i=0; i<2; ++i) {
      // Update sequential element outputs
      for (auto& vd : gr.getVerts()) {
        WireNode wd = gr.getNode(vd);

        if (isMemoryInstance(wd.getWire()) && !wd.isReceiver) {
          // Does this work when the raddr port is not yet defined?
          updateMemoryOutput(vd);
        }

      if (isRegisterInstance(wd.getWire()) && !wd.isReceiver) {
        updateRegisterOutput(vd);
      }

        if (isDFFInstance(wd.getWire()) && !wd.isReceiver) {
          updateDFFOutput(vd);
        }
        
      }

      if (!hasCombinationalLoop) {
        // Update combinational node values
        for (auto& vd : topoOrder) {
          updateNodeValues(vd);
        }
      } else {

        //ASSERT(!hasCombinationalLoop, "Circuits in the interpreter cannot have combinational loops");

        set<vdisc> freshNodes;
        // Initially all inputs are fresh
        for (auto& vd : gr.getVerts()) {
          WireNode w = gr.getNode(vd);

          if (isGraphInput(w)) {
            freshNodes.insert(vd);
          }
        }

        CircuitState lastState = getCircStates().back();
        while (freshNodes.size() > 0) {
          vdisc vd = *std::begin(freshNodes);
          Wireable* w = gr.getNode(vd).getWire();
          freshNodes.erase(vd);

          unordered_map<Select*, SimValue*> oldVals = lastState.valMap;
          assert(gr.containsOpNode(w));

          // Need to update and check whether the update actually changed any of
          // the outputs of this wire

          updateNodeValues(vd);

          unordered_map<Select*, SimValue*> currentVals = lastState.valMap;

          // This check doesnt deal with changed inputs.
          bool outputsChanged = false;
          if (currentVals.size() != oldVals.size()) {
            outputsChanged = true;
          } else {
            for (auto v : oldVals) {
              assert(contains_key(v.first, currentVals));
              if (*(v.second) != *(currentVals.find(v.first)->second)) {
                outputsChanged = true;
                break;
              }
            }
          }

          if (!outputsChanged) {
            continue;
          }

          for (auto outEdge : gr.outEdges(vd)) {
            vdisc wd = gr.target(outEdge);

            // Sequential elements dont get updated in this function
            if (gr.containsOpNode(gr.getNode(wd).getWire())) {
              freshNodes.insert(wd);
            }
          }

        }
      }
    }
  }

  void SimulatorState::execute() {
    assert(atLastState());

    CircuitState next = circStates[stateIndex];
    circStates.push_back(next);
    stateIndex++;

    vector<vdisc> unsetIns = unsetInputs();
    if (unsetIns.size() > 0) {
      cout << "Cannot execute because " << unsetIns.size() << " input(s) are not set:" << endl;
      for (auto& vd : unsetIns) {
        cout << "\t" << getCircuitGraph().getNode(vd).getWire()->toString() << endl;
      }
      return;
    }

    if (hasMainClock()) {
      ClockValue* clockCopy = new ClockValue(*toClock(getValue(mainClock)));
      allocatedValues.insert(clockCopy);
      setValue(mainClock, clockCopy);
    }

    exeCombinational();
    exeSequential();
    exeCombinational();

  }

  void SimulatorState::setClock(const std::vector<std::string> &path,
                                const unsigned char clk_last,
                                const unsigned char clk) {
    string name = concatInlined(path);
    setClock(name, clk_last, clk);
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

  string
  reconstructName(const std::vector<std::string>& instanceList,
                  const std::vector<std::string>& portSelectList) {
    string selectVal = concatSelects(portSelectList);
    vector<string> insts = instanceList;
    insts[insts.size() - 1] =
      insts[insts.size() - 1] + "." + selectVal;
    string name = concatInlined(insts);

    return name;
  }

  void SimulatorState::deleteWatchPointByOriginalName(const std::vector<std::string>& instanceList,
                                                      const std::vector<std::string>& portSelectList) {
    string originalName = reconstructName(instanceList, portSelectList);
    deleteWatchPoint(originalName);
  }

  void
  SimulatorState::setWatchPointByOriginalName(const std::string& name,
                                              const BitVec& bv) {
    setWatchPoint(name, bv);
  }

  void
  SimulatorState::setWatchPointByOriginalName(const std::vector<std::string>& instanceList,
                                              const std::vector<std::string>& portSelectList,
                                              const BitVec& bv) {
    string originalName = reconstructName(instanceList, portSelectList);

    setWatchPointByOriginalName(originalName, bv);
  }

  SimValue*
  SimulatorState::getValueByOriginalName(const std::vector<std::string>& instanceList,
                                         const std::vector<std::string>& portSelectList) {
    string name = reconstructName(instanceList, portSelectList);
    return getValueByOriginalName(name);
  }

  bool isPrefixOf(const std::string& foo,
                  const std::string& foobar) {
    auto res = std::mismatch(foo.begin(), foo.end(), foobar.begin());

    if (res.first == foo.end()) {
      return true;
    }

    return false;
  }

  std::vector<string>
  selectsOffOf(const std::string& selectName,
               std::map<std::string, json>& symTable) {

    vector<string> sels;

    for (auto& ent : symTable) {
      string selName = ent.first;
      if (isPrefixOf(selectName, selName)) {
        sels.push_back(selName);
      }
    }

    return sels;
  }

  SimValue*
  SimulatorState::getValueByOriginalName(const std::string& name) {
    
    SimValue* val = getValue(name);

    // Case 1: The value being requested exists in the simulator code
    if (val != nullptr) {
      return val;
    }

    // Case 2: The value being requested has an entry in the symbol table
    if (symTable.count(name) > 0) {
      SelectPath ent = symTable[name];
      string entName = concatSelects(ent);

      //cout << "Entry name = " << entName << endl;
      return getValueByOriginalName(entName);
    }

    // Case 3: The value does not have a symbol table entry. 3 subcases:
    //      1. The value is invalid
    //      2. Need to traverse up the type hierarchy
    //      3. Need to traverse down the type hierarchy

    //cout << name << " is not a key in the symbol table" << endl;
    //cout << "Selects off of this name" << endl;
    vector<string> postFixes =
      selectsOffOf(name, symTable);

    // Handle the case where the underlying value is an array
    if (postFixes.size() > 0) {

      SelectPath namePath = splitString<SelectPath>(name,'.');
      for (auto& sp : postFixes) {
        SelectPath sPath = splitString<SelectPath>(sp,'.');
        assert(sPath.size() == (namePath.size() + 1));

        string lastSelStr = sPath.back();

        assert(isNumber(lastSelStr));

        //cout << sp << endl;
      }

      // At this point we know that the result will be an array
      // We are assuming that it is an array of bits
      //cout << "Result is an array of length " << postFixes.size() << endl;

      BitVector result(postFixes.size());

      for (auto& sp : postFixes) {
        SelectPath sPath = splitString<SelectPath>(sp,'.');
        string lastSelStr = sPath.back();

        SimValue* sv = getValueByOriginalName(sp);
        // assert(sv->getType() == SIM_VALUE_BV);

        // SimBitVector* sbv = static_cast<SimBitVector*>(sv);

        auto sbv = toSimBitVector(sv);

        BitVector sbits = sbv->getBits();

        assert(sbits.bitLength() == 1);

        int index = stoi(lastSelStr);
        result.set(index, sbits.get(0));
      }

      return makeSimBitVector(result);
    }

    SelectPath namePath = splitString<SelectPath>(name, '.');
    string access = namePath.back();
    namePath.pop_back();

    SimValue* sv = getValueByOriginalName(concatSelects(namePath));
    auto sbv = toSimBitVector(sv);

    BitVector finalBv(1, 0);
    finalBv.set(0, sbv->getBits().get(stoi(access)));
    return makeSimBitVector(finalBv);

  }

  SimulatorState::~SimulatorState() {
    for (auto& val : allocatedValues) {
      delete val;
    }
  }

}
