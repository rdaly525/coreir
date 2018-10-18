#pragma once

#include "coreir/simulator/op_graph.h"
#include "coreir/ir/dynamic_bit_vector.h"
#include "coreir/ir/value.h"

namespace CoreIR {

  typedef bsim::quad_value_bit_vector BitVec;

  enum SimValueType {
    SIM_VALUE_BV,
    SIM_VALUE_CLK
  };

  class SimMemory {
  protected:
    std::map<BitVec, BitVec> values;

    uint width;
    uint depth;

  public:

    SimMemory(const uint width_, const uint depth_) :
      width(width_), depth(depth_)
    {}

    std::map<BitVec, BitVec>::const_iterator begin() const {
      return std::begin(values);
    }

    std::map<BitVec, BitVec>::const_iterator end() const {
      return std::end(values);
    }

    BitVec getAddr(const BitVec& bv) const;
    void setAddr(const BitVec& bv, const BitVec& val);
  };

  class SimValue {
  public:
    virtual ~SimValue() {}

    virtual SimValueType getType() const = 0;

    virtual bool operator==(const SimValue& other) const = 0;

    virtual bool operator!=(const SimValue& other) const {
      return !((*this) == other);
    }
  };

  class SimBitVector : public SimValue {
  protected:
    BitVec bv;

  public:
    SimBitVector(const BitVec& bv_) : bv(bv_) {}

    BitVec getBits() const { return bv; }

    virtual SimValueType getType() const { return SIM_VALUE_BV; }

    virtual bool operator==(const SimValue& other) const {
      if (other.getType() != SIM_VALUE_BV) {
        return false;
      }
      const SimBitVector& otherBit = static_cast<const SimBitVector&>(other);

      return this->getBits() == otherBit.getBits();
    }
  };

  class ClockValue : public SimValue {
  protected:
    unsigned char lastVal, val;
    int halfCycleCount;

  public:
    ClockValue(const unsigned char lastVal_,
	       const unsigned char val_) : lastVal(lastVal_), val(val_), halfCycleCount(0) {}

    unsigned char value() const { return val; }
    unsigned char lastValue() const { return lastVal; }

    void flip() {
      unsigned char tmp = lastVal;
      lastVal = val;
      val = tmp;
      halfCycleCount++;
    }

    int getCycleCount() const { return halfCycleCount / 2; }
    int getHalfCycleCount() const { return halfCycleCount; }

    virtual SimValueType getType() const { return SIM_VALUE_CLK; }

    virtual bool operator==(const SimValue& other) const {
      if (other.getType() != SIM_VALUE_CLK) {
        return false;
      }
      const ClockValue& otherBit = static_cast<const ClockValue&>(other);

      // Q: Should we compare half cycle counts?
      return (this->value() == otherBit.value()) &&
        (this->lastValue() == otherBit.lastValue());
    }
    
  };

  class CircuitState {
  public:
    // Wire values
    std::unordered_map<CoreIR::Select*, SimValue*> valMap;

    // Internal state of the circuit
    std::unordered_map<std::string, SimMemory> memories;
    std::unordered_map<std::string, BitVec> registers;
    
  };

  typedef BitVec (*BitVecBinop)(const BitVec& l, const BitVec& r);
  typedef BitVec (*BitVecUnop)(const BitVec& l);

  typedef std::function<bool()> StopFunction;

  struct StopCondition {
    std::string name;
    StopFunction stopTest;
  };

  class SimulatorState {
    CoreIR::Module* mod;
    std::map<std::string, json> symTable;
    bool hasSymTable;

    NGraph gr;
    std::deque<vdisc> topoOrder;

    std::vector<StopCondition> stopConditions;

    CoreIR::Select* mainClock;

    std::vector<CircuitState> circStates;
    int stateIndex;

    std::set<SimValue*> allocatedValues;

    bool hasCombinationalLoop;

  public:

    SimulatorState(CoreIR::Module* mod_);

    int numCircStates() const;

    void findMainClock();
    void setInputDefaults();
    std::vector<vdisc> unsetInputs();

    std::vector<CircuitState> getCircStates() const;

    NGraph& getCircuitGraph() { return gr; }

    SimBitVector* makeSimBitVector(const BitVector& bv);

    int getStateIndex() const;
    
    bool valMapContains(CoreIR::Select* sel) const;

    bool hitWatchPoint() const;

    void setMainClock(const std::string& val);
    CoreIR::Select* getMainClock() { return mainClock; }

    void setMainClock(CoreIR::Select* s);

    bool hasMainClock() const { return mainClock != nullptr; }

    void setMainClock(const std::vector<std::string>& path);

    bool rewind(const int halfCycles);

    void updateInputs(const vdisc vd);    

    CoreIR::Select* findSelect(const std::string& name) const;

    bool atLastState();
    void runHalfCycle();
    void stepMainClock();
    void stepClock(const std::string& str);
    void stepClock(CoreIR::Select* clkSelect);

    void setWatchPoint(const std::string& val,
		       const BitVec& bv);
    void setWatchPoint(const std::vector<std::string>& path,
		       const BitVec& bv);

    void deleteWatchPoint(const std::string& name);

    void setDFFDefaults();
    void updateDFFOutput(const vdisc vd);
    void updateDFFValue(const vdisc vd);

    void updateMemoryOutput(const vdisc vd);
    void setConstantDefaults();
    void setRegisterDefaults();
    // void setLineBufferMem(const std::string& name,
    //     		  const BitVector& data);

    void updateLinebufferMemOutput(const vdisc vd);
    void setMemoryDefaults();
    //void setLinebufferMemDefaults();

    void updateBitVecUnop(const vdisc vd, BitVecUnop op);
    void updateBitVecBinop(const vdisc vd, BitVecBinop op);

    // bool lineBufferOutIsValid(const std::string& memName);
    // BitVector getLinebufferValue(const std::string& memName);

    void setValue(CoreIR::Select* sel, SimValue* val);
    void setValue(CoreIR::Select* sel, const BitVec& bv);
    void setValue(const std::string& name, const BitVec& bv);
    void setValue(const std::vector<std::string>& name, const BitVec& bv);

    void setClock(CoreIR::Select* sel,
		  const unsigned char clk_last,
		  const unsigned char clk);

    void setClock(const std::string& name,
		  const unsigned char clk_last,
		  const unsigned char clk);

    void setClock(const std::vector<std::string>& path,
                  const unsigned char clk_last,
                  const unsigned char clk);

    void setRegister(const std::string& name,
                     const BitVec& data);

    BitVec getRegister(const std::string& name);
    
    void setMemory(const std::string& name,
		   const BitVec& addr,
		   const BitVec& data);

    BitVec getMemory(const std::string& name,
		     const BitVec& addr);

    bool exists(const std::string& selStr) const;
    bool isSet(const std::string& selStr) const;
    bool isSet(CoreIR::Select* s) const;

    SimValue* getValue(const std::string& name);
    SimValue* getValue(CoreIR::Select* sel);
    SimValue* getValue(const std::vector<std::string>& str);

    BitVec getBitVec(CoreIR::Select* sel);
    BitVec getBitVec(const std::string& str);
    BitVec getBitVec(const std::vector<std::string>& str);

    void updateRegisterOutput(const vdisc vd);

    void updateRegisterValue(const vdisc vd);
    void updateMemoryValue(const vdisc vd);
    //void updateLinebufferMemValue(const vdisc vd);

    void updateOrrNode(const vdisc vd);
    void updateZextNode(const vdisc vd);
    void updateLUTNNode(const vdisc vd);
    void updateMuxNode(const vdisc vd);
    void updateAddNode(const vdisc vd);
    void updateNeqNode(const vdisc vd);
    void updateEqNode(const vdisc vd);    
    void updateConcatNode(const vdisc vd);
    void updateSliceNode(const vdisc vd);    
    void updateAndrNode(const vdisc vd);
    void updateOutput(const vdisc vd);
    void updateOrNode(const vdisc vd);
    void updateAndNode(const vdisc vd);
    void updateNodeValues(const vdisc vd);

    void exeSequential();
    void exeCombinational();
    void execute();

    void resetCircuit();

    void run();
    void runBack();

    // Symbol table lookup
    SimValue*
    getValueByOriginalName(const std::vector<std::string>& instanceList,
                           const std::vector<std::string>& portSelectList);

    SimValue*
    getValueByOriginalName(const std::string& name);

    void
    deleteWatchPointByOriginalName(const std::vector<std::string>& instanceList,
                                const std::vector<std::string>& portSelectList);

    void
    setWatchPointByOriginalName(const std::vector<std::string>& instanceList,
                                const std::vector<std::string>& portSelectList,
                                const BitVec& value);

    void
    setWatchPointByOriginalName(const std::string& name,
                                const BitVec& bv);

    // Destructor

    ~SimulatorState();
  };

  ClockValue* toClock(SimValue* val);
  SimBitVector* toSimBitVector(SimValue* v);

  std::string concatInlined(const std::vector<std::string>& str);
  std::string concatSelects(const std::deque<std::string>& str);
  std::string concatSelects(const std::vector<std::string>& str);

}
