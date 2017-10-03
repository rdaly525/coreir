#include "interpret.hpp"

namespace CoreIR {

  void SimulatorState::setValue(CoreIR::Select* sel, const BitVec& bv) {
    
  }

  BitVec SimulatorState::getValue(CoreIR::Select* sel) {
    return BitVec(32, 0);
  }

  void SimulatorState::execute() {
    
  }
}
