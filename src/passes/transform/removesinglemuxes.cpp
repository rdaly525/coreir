#include "coreir/passes/transform/removesinglemuxes.h"
#include "coreir/common/util.h"

using namespace std;
using namespace CoreIR;

namespace CoreIR {

  namespace Passes {

    string Passes::RemoveSingleMuxes::ID = "removesinglemuxes";
    bool RemoveSingleMuxes::runOnModule(Module* m) {
      if (!m->hasDef()) {
        return false;
      }

      cout << "Processing module " << m->getName() << endl;

      ModuleDef* def = m->getDef();
      for (auto instR : def->getInstances()) {
        auto inst = instR.second;
        printf("here!\n");

        if (getQualifiedOpName(*inst) == "commonlib.muxn") {
          //int n = inst->getModArgs().at("N")->get<int>();
          printf("%d\n", 1);
        } else {
            printf("here again!\n");
        }
      }
      return true;
    }
  }
}
