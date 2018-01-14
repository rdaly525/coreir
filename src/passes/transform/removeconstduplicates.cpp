#include "coreir/passes/transform/removeconstduplicates.h"

using namespace std;
using namespace CoreIR;

namespace CoreIR {

  namespace Passes {

    string Passes::RemoveConstDuplicates::ID = "removeconstduplicates";
    bool RemoveConstDuplicates::runOnModule(Module* m) {
      if (!m->hasDef()) {
        return false;
      }

      cout << "Processing module " << m->getName() << endl;

      Instance* bitConstZero = nullptr;
      Instance* bitConstOne = nullptr;
      
      return false;
    }
  }
}
