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

  class BitVector : public SimValue {
  protected:
    BitVec bv;

  public:
    BitVector(const BitVec& bv_) : bv(bv_) {}

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

  class CircuitState {
  public:
    std::unordered_map<CoreIR::Select*, SimValue*> valMap;
    std::unordered_map<std::string, SimMemory> memories;

  };

  class SimulatorState {
    CoreIR::Module* mod;

    NGraph gr;
    std::deque<vdisc> topoOrder;
    std::vector<std::pair<std::string, BitVec> > watchPoints;
    CoreIR::Select* mainClock;

    std::vector<CircuitState> circStates;
    int stateIndex;

  public:

    SimulatorState(CoreIR::Module* mod_);

    std::vector<CircuitState> getCircStates() const;

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

    void updateMemoryOutput(const vdisc vd);
    void setConstantDefaults();
    void setRegisterDefaults();
    void setMemoryDefaults();

    void setValue(CoreIR::Select* sel, SimValue* val);
    void setValue(CoreIR::Select* sel, const BitVec& bv);
    void setValue(const std::string& name, const BitVec& bv);

    void setClock(CoreIR::Select* sel,
		  const unsigned char clk_last,
		  const unsigned char clk);

    void setClock(const std::string& name,
		  const unsigned char clk_last,
		  const unsigned char clk);

    void setMemory(const std::string& name,
		   const BitVec& addr,
		   const BitVec& data);

    BitVec getMemory(const std::string& name,
		     const BitVec& addr);

    bool isSet(const std::string& selStr) const;

    SimValue* getValue(const std::string& name) const;
    SimValue* getValue(CoreIR::Select* sel) const;
    BitVec getBitVec(CoreIR::Select* sel) const;

    BitVec getBitVec(const std::string& str) const;

    void updateMuxNode(const vdisc vd);
    void updateRegisterValue(const vdisc vd);
    void updateMemoryValue(const vdisc vd);
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

}
