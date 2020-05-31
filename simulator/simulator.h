#pragma once

#include "utils/wiring_utils.h"
#include "simulator/codegen.h"
#include "simulator/layout.h"
#include "simulator/multithreading.h"
#include "simulator/subcircuit.h"

namespace CoreIR {

std::string printSimFunctionBody(
  const std::deque<vdisc>& topo_order,
  NGraph& g,
  Module& mod,
  const int threadNo,
  const LayoutPolicy& layoutPolicy);

std::string printCode(const ModuleCode& mc);

ModuleCode buildCode(
  const std::deque<vdisc>& topoOrder,
  NGraph& g,
  CoreIR::Module* mod,
  const std::string& baseName);

std::string printDecl(const ModuleCode& mc);

std::vector<std::pair<CoreIR::Type*, std::string>> sortedSimArgumentPairs(
  Module& mod);

ThreadGraph buildThreadGraph(const NGraph& opG);

std::string seMacroDef();
std::string maskMacroDef();

}  // namespace CoreIR
