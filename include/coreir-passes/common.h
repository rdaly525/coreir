#ifndef PASSES_COMMON_H_
#define PASSES_COMMON_H_

//Analysis passes
#include "analysis/helloa.h"
#include "analysis/constructinstancegraph.h"
#include "analysis/firrtl.h"

//Transform passes
#include "transform/hellot.h"
#include "transform/flatten.h"
#include "transform/rungenerators.h"


//TODO Macrofy this
namespace CoreIR {
  void initializePasses(PassManager& pm) {
    //Analysis
    pm.addPass(new Passes::HelloA());
    pm.addPass(new Passes::ConstructInstanceGraph());
    pm.addPass(new Passes::Firrtl());
    
    //Transform
    pm.addPass(new Passes::HelloT());
    pm.addPass(new Passes::Flatten());
    pm.addPass(new Passes::RunGenerators());
  }
}

#endif //PASSES_HPP_
