#include "coreir.h"
#include "coreir/common/logging_lite.hpp"
#include "coreir/passes/transform/rungenerators.h"

using namespace CoreIR;

std::string Passes::RunGenerators::ID = "rungenerators";

bool Passes::RunGenerators::runOnContext(Context* c) {
  LOG(INFO) << "In Run Generators";
  bool changed = true;
  bool modified = false;
  while (changed) {
    changed = false;
    for (auto npair : c->getNamespaces()) {
      for (auto gpair : npair.second->getGenerators()) {
        for (auto mpair : gpair.second->getGeneratedModules()) {
          changed |= mpair.second->runGenerator();
        }
      }
    }

    modified |= changed;
  }

  LOG(INFO) << "Done running generators";

  return modified;
  
}
