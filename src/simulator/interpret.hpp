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
    NGraph gr;
    std::unordered_map<CoreIR::Select*, SimValue*> valMap;
    std::deque<vdisc> topoOrder;    

  public:

    SimulatorState(CoreIR::Module* mod);

    void setValue(CoreIR::Select* sel, const BitVec& bv);

    BitVec getValue(CoreIR::Select* sel);

    void updateOutput(const vdisc vd);
    void updateAndNode(const vdisc vd);
    void updateNodeValues(const vdisc vd);
    void execute();

    ~SimulatorState();
  };

}
