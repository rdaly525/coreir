#pragma once

#include "coreir.h"
#include "dynamic_bit_vector.h"

namespace CoreIR {

  typedef bsim::dynamic_bit_vector BitVec;

  class SimulatorState {

  public:

    void setValue(CoreIR::Select* sel, const BitVec& bv);

    BitVec getValue(CoreIR::Select* sel);

    void execute();

  };

}
