#ifndef PASSES_COMMON_H_
#define PASSES_COMMON_H_

//Analysis passes
#include "analysis/helloa.h"
#include "analysis/constructinstancegraph.h"
#include "analysis/firrtl.h"
#include "analysis/verilog.h"

//Transform passes
#include "transform/hellot.h"
#include "transform/flatten.h"
#include "transform/rungenerators.h"
#include "transform/flattentypes.h"
#include "transform/removebulkconnections.h"


//TODO Macrofy this
namespace CoreIR {
  void initializePasses(PassManager& pm) {
    //Analysis
    pm.addPass(new Passes::HelloA());
    pm.addPass(new Passes::ConstructInstanceGraph());
    pm.addPass(new Passes::Firrtl());
    pm.addPass(new Passes::Verilog());
    
    //Transform
    pm.addPass(new Passes::HelloT());
    pm.addPass(new Passes::Flatten());
    pm.addPass(new Passes::RunGenerators());
    pm.addPass(new Passes::FlattenTypes());
    pm.addPass(new Passes::RemoveBulkConnections());
  }
}

#endif //PASSES_HPP_
