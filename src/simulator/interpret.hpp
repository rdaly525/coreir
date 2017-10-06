#pragma once

#include "coreir.h"
#include "dynamic_bit_vector.h"
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

  public:

    BitVec getAddr(const BitVec& bv) const {
      auto it = values.find(bv);

      if (it == std::end(values)) {
	//assert(false);
	return BitVec(1, 0);
      }

      return it->second;
    }
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

    virtual SimValueType getType() const { return SIM_VALUE_CLK; }
  };

  class SimulatorState {
    CoreIR::Module* mod;
    NGraph gr;
    std::unordered_map<CoreIR::Select*, SimValue*> valMap;
    std::deque<vdisc> topoOrder;

    std::unordered_map<std::string, SimMemory> memories;

  public:

    SimulatorState(CoreIR::Module* mod_);

    void updateMemoryOutput(const vdisc vd);
    void setConstantDefaults();
    void setMemoryDefaults();

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
	    
    SimValue* getValue(const std::string& name);
    SimValue* getValue(CoreIR::Select* sel);
    BitVec getBitVec(CoreIR::Select* sel);

    BitVec getBitVec(const std::string& str);

    void updateMuxNode(const vdisc vd);
    void updateRegisterValue(const vdisc vd);
    void updateMemoryValue(const vdisc vd);
    void updateAddNode(const vdisc vd);
    void updateOutput(const vdisc vd);
    void updateOrNode(const vdisc vd);
    void updateAndNode(const vdisc vd);
    void updateNodeValues(const vdisc vd);
    void execute();

    ~SimulatorState();
  };

  ClockValue* toClock(SimValue* val);

}
