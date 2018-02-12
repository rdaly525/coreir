#include "coreir.h"
#include "coreir/passes/transform/rungenerators.h"

using namespace std;
using namespace CoreIR;

string Passes::RunGenerators::ID = "rungenerators";
bool Passes::RunGenerators::runOnContext(Context* c) {
  cout << "In Run Generators" << endl;
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

  cout << "Done running generators" << endl;

  return modified;
  
}
