#ifndef PASSES_COMMON_H_
#define PASSES_COMMON_H_

//Analysis passes
#include "analysis/helloa.h"
#include "analysis/constructinstancegraph.h"

//Transform passes
#include "transform/hellot.h"
#include "transform/flatten.h"


//Macrofy this
namespace CoreIR {
  void initializePasses(PassManager& pm) {
    pm.addPass(new Passes::HelloA());
    pm.addPass(new Passes::ConstructInstanceGraph());
    pm.addPass(new Passes::HelloT());
    pm.addPass(new Passes::Flatten());
  }
}

#undef ADDPASS

#endif //PASSES_HPP_
