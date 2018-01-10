#pragma once

#include "coreir/ir/module.h"
#include "coreir/ir/wireable.h"

namespace CoreIR {

  std::vector<CoreIR::Wireable*>
  extractSubcircuit(CoreIR::Module* mod,
                    const std::vector<Wireable*>& startingPorts);

}
