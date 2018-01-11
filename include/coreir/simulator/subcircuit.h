#pragma once

#include "coreir/ir/module.h"
#include "coreir/ir/wireable.h"

namespace CoreIR {

  std::vector<CoreIR::Instance*>
  extractSubcircuit(CoreIR::Module* mod,
                    const std::vector<Wireable*>& startingPorts);

  void
  addSubcircuitModule(const std::string& moduleName,
                      CoreIR::Module* const srcModule,
                      const std::vector<Wireable*>& selfPorts,
                      const std::vector<CoreIR::Instance*>& instances,
                      CoreIR::Context* const c,
                      CoreIR::Namespace* const g);
  
}
