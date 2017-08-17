#include "coreir.h"
#include "coreir-passes/analysis/constructinstancegraph.h"

using namespace CoreIR;

std::string Passes::ConstructInstanceGraph::ID = "constructInstanceGraph";
bool Passes::ConstructInstanceGraph::runOnNamespace(Namespace* ns) {
  ig->construct(ns);
  return false;
}
void Passes::ConstructInstanceGraph::releaseMemory() {
  ig->releaseMemory();
}
