#ifndef PASSES_COMMON_H_
#define PASSES_COMMON_H_

//Analysis passes
#include "analysis/helloa.h"
#include "analysis/constructinstancegraph.h"
#include "analysis/firrtl.h"
#include "analysis/verilog.h"
#include "analysis/coreirjson.h"
#include "analysis/weakverify.h"
#include "analysis/strongverify.h"
#include "analysis/verifyflattenedtypes.h"
#include "analysis/createinstancemap.h"

//Transform passes
#include "transform/hellot.h"
#include "transform/flatten.h"
#include "transform/rungenerators.h"
#include "transform/flattentypes.h"
#include "transform/removebulkconnections.h"
#include "transform/liftclockports.h"
#include "transform/wireclocks.h"


//TODO Macrofy this
namespace CoreIR {
  void initializePasses(PassManager& pm) {
    Context* c = pm.getContext();
    //Analysis
    pm.addPass(new Passes::HelloA());
    pm.addPass(new Passes::ConstructInstanceGraph());
    pm.addPass(new Passes::CreateInstanceMap());
    pm.addPass(new Passes::Firrtl());
    pm.addPass(new Passes::CoreIRJson());
    pm.addPass(new Passes::Verilog());
    pm.addPass(new Passes::WeakVerify());
    pm.addPass(new Passes::StrongVerify());
    pm.addPass(new Passes::VerifyFlattenedTypes());
    
    //Transform
    pm.addPass(new Passes::HelloT());
    pm.addPass(new Passes::Flatten());
    pm.addPass(new Passes::RunGenerators());
    pm.addPass(new Passes::FlattenTypes());
    pm.addPass(new Passes::RemoveBulkConnections());
    pm.addPass(new Passes::LiftClockPorts("liftclockports-coreir",c->Named("coreir","clkIn")));
    pm.addPass(new Passes::WireClocks("wireclocks-coreir",c->Named("coreir","clkIn")));
  }
}

#endif //PASSES_HPP_
