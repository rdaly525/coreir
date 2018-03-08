#pragma once

#include "coreir/simulator/interpreter.h"
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

  bool foldConstants(CoreIR::Module* const mod);

  void registersToConstants(CoreIR::Module* const mod,
                            std::unordered_map<std::string, BitVec>& regValues);

  void partiallyEvaluateCircuit(CoreIR::Module* const wholeTopMod,
                                std::unordered_map<std::string, BitVector>& regMap);

  Module* createSubCircuit(CoreIR::Module* const topMod,
                           std::vector<CoreIR::Wireable*>& subCircuitPorts,
                           std::vector<CoreIR::Instance*>& subCircuitInstances,
                           CoreIR::Context* const c);
  
}
