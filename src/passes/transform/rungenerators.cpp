#include "coreir/passes/transform/rungenerators.h"
#include "coreir.h"
#include "coreir/common/logging_lite.hpp"

using namespace CoreIR;

bool Passes::RunGenerators::runOnContext(Context* c) {
  LOG(DEBUG) << "In Run Generators";
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

  LOG(DEBUG) << "Done running generators";

  return modified;
}
