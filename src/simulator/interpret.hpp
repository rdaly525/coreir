#pragma once

#include "coreir.h"
#include "dynamic_bit_vector.h"
#include "op_graph.hpp"


namespace CoreIR {

  typedef bsim::dynamic_bit_vector BitVec;

  class SimValue {
  public:
    ~SimValue() {}
  };

  class BitVector : public SimValue {
  protected:
    BitVec bv;

  public:
    BitVector(const BitVec& bv_) : bv(bv_) {}

    BitVec getBits() const { return bv; }
  };

  class SimulatorState {
    CoreIR::Module* mod;
    NGraph gr;
    std::unordered_map<CoreIR::Select*, SimValue*> valMap;
    std::deque<vdisc> topoOrder;    

  public:

    SimulatorState(CoreIR::Module* mod_);

    void setValue(CoreIR::Select* sel, const BitVec& bv);
    void setValue(const std::string& name, const BitVec& bv);

    void setClock(CoreIR::Select* sel,
		  const unsigned char clk_last,
		  const unsigned char clk);

  void setClock(const std::string& name,
		const unsigned char clk_last,
		const unsigned char clk);
    
    SimValue* getValue(CoreIR::Select* sel);
    BitVec getBitVec(CoreIR::Select* sel);

    BitVec getBitVec(const std::string& str);

    void updateAddNode(const vdisc vd);
    void updateOutput(const vdisc vd);
    void updateOrNode(const vdisc vd);
    void updateAndNode(const vdisc vd);
    void updateNodeValues(const vdisc vd);
    void execute();

    ~SimulatorState();
  };

}
