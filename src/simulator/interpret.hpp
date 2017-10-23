#pragma once

#include "coreir.h"
#include "op_graph.hpp"


namespace CoreIR {

  typedef bsim::dynamic_bit_vector BitVec;

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
  };

  class SimBitVector : public SimValue {
  protected:
    BitVec bv;

  public:
    SimBitVector(const BitVec& bv_) : bv(bv_) {}

    BitVec getBits() const { return bv; }

    virtual SimValueType getType() const { return SIM_VALUE_BV; }
  };

  class ClockValue : public SimValue {
  protected:
    unsigned char lastVal, val;

  public:
    ClockValue(const unsigned char lastVal_,
	       const unsigned char val_) : lastVal(lastVal_), val(val_) {}

    unsigned char value() const { return val; }
    unsigned char lastValue() const { return lastVal; }

    void flip() {
      unsigned char tmp = lastVal;
      lastVal = val;
      val = tmp;
    }

    virtual SimValueType getType() const { return SIM_VALUE_CLK; }
  };

  class LinebufferMemory {
    std::deque<BitVector> values;
    std::deque<bool> valids;
    int width, depth;

  public:

    LinebufferMemory(const int width_, const int depth_) :
      width(width_), depth(depth_) {

      for (int i = 0; i < getDepth(); i++) {
	values.push_back(BitVector(width, 0));
	valids.push_back(false);
      }

      assert(((int)values.size()) == depth);
    }

    BitVector peek() const {
      assert(((int)values.size()) == depth);

      return values[getDepth() - 1];
    }

    bool isValid() const {
      assert(((int)valids.size()) == depth);
      return valids.back();
    }

    BitVector push(const BitVector& vec) {
      values.push_front(vec);
      valids.push_front(true);

      BitVector toRet = values.back();
      values.pop_back();
      valids.pop_back();

      assert(((int)values.size()) == depth);
      assert(((int)valids.size()) == depth);

      return toRet;
    }

    int getDepth() const { return depth; }
  };

  class CircuitState {
  public:
    // Wire values
    std::unordered_map<CoreIR::Select*, SimValue*> valMap;

    // Internal state of the circuit
    std::unordered_map<std::string, SimMemory> memories;
    std::unordered_map<std::string, BitVec> registers;
    std::unordered_map<std::string, LinebufferMemory> lbMemories;
    
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

    NGraph gr;
    std::deque<vdisc> topoOrder;

    std::vector<StopCondition> stopConditions;

    CoreIR::Select* mainClock;

    std::vector<CircuitState> circStates;
    int stateIndex;

    std::set<SimValue*> allocatedValues;

  public:

    SimulatorState(CoreIR::Module* mod_);

    int numCircStates() const;

    std::vector<CircuitState> getCircStates() const;

    NGraph& getCircuitGraph() { return gr; }

    SimBitVector* makeSimBitVector(const BitVector& bv);

    int getStateIndex() const;
    
    bool valMapContains(CoreIR::Select* sel) const;

    bool hitWatchPoint() const;

    void setMainClock(const std::string& val);

    bool rewind(const int halfCycles);

    CoreIR::Select* findSelect(const std::string& name) const;

    bool atLastState();
    void runHalfCycle();
    void stepMainClock();
    void stepClock(const std::string& str);
    void stepClock(CoreIR::Select* clkSelect);

    void setWatchPoint(const std::string& val,
		       const BitVec& bv);

    void deleteWatchPoint(const std::string& name);

    void updateMemoryOutput(const vdisc vd);
    void setConstantDefaults();
    void setRegisterDefaults();
    void setLineBufferMem(const std::string& name,
			  const BitVector& data);

    void updateLinebufferMemOutput(const vdisc vd);
    void setMemoryDefaults();
    void setLinebufferMemDefaults();

    void updateBitVecUnop(const vdisc vd, BitVecUnop op);
    void updateBitVecBinop(const vdisc vd, BitVecBinop op);

    bool lineBufferOutIsValid(const std::string& memName);
    BitVector getLinebufferValue(const std::string& memName);

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

    void updateRegisterValue(const vdisc vd);
    void updateMemoryValue(const vdisc vd);
    void updateLinebufferMemValue(const vdisc vd);

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

    void execute();

    void run();

    ~SimulatorState();
  };

  ClockValue* toClock(SimValue* val);

  std::string concatInlined(const std::vector<std::string>& str);

}
