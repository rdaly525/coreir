#include "passes/transform/rungenerators.h"
#include "ir/coreir.h"
#include "common/logging_lite.hpp"

using namespace CoreIR;

std::string Passes::RunGenerators::ID = "rungenerators";

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
