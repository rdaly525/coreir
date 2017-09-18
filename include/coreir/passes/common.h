#ifndef PASSES_COMMON_H_
#define PASSES_COMMON_H_

//Analysis passes
#include "analysis/hellomodule.h"
#include "analysis/createinstancegraph.h"
#include "analysis/firrtl.h"
#include "analysis/verilog.h"
#include "analysis/coreirjson.h"
#include "analysis/verifyconnectivity.h"
#include "analysis/verifyinputconnections.h"
#include "analysis/verifyflattenedtypes.h"
#include "analysis/createmodinstancemap.h"
#include "analysis/createfullinstancemap.h"

//Transform passes
#include "transform/flatten.h"
#include "transform/rungenerators.h"
#include "transform/flattentypes.h"
#include "transform/removebulkconnections.h"
#include "transform/removeunconnected.h"
#include "transform/liftclockports.h"
#include "transform/wireclocks.h"


//TODO Macrofy this
namespace CoreIR {
  void initializePasses(PassManager& pm) {
    Context* c = pm.getContext();
    //Analysis
    pm.addPass(new Passes::HelloModule());
    pm.addPass(new Passes::CreateInstanceGraph());
    pm.addPass(new Passes::CreateModInstanceMap());
    pm.addPass(new Passes::CreateFullInstanceMap());
    pm.addPass(new Passes::Firrtl());
    pm.addPass(new Passes::CoreIRJson());
    pm.addPass(new Passes::Verilog());
    pm.addPass(new Passes::VerifyInputConnections());
    pm.addPass(new Passes::VerifyConnectivity(true,true));
    pm.addPass(new Passes::VerifyConnectivity(true,false));
    pm.addPass(new Passes::VerifyConnectivity(false,true));
    pm.addPass(new Passes::VerifyConnectivity(false,false));
    pm.addPass(new Passes::VerifyFlattenedTypes());
    
    //Transform
    pm.addPass(new Passes::Flatten());
    pm.addPass(new Passes::RunGenerators());
    pm.addPass(new Passes::FlattenTypes());
    pm.addPass(new Passes::RemoveBulkConnections());
    pm.addPass(new Passes::RemoveUnconnected());
    pm.addPass(new Passes::LiftClockPorts("liftclockports-coreir",c->Named("coreir.clkIn")));
    pm.addPass(new Passes::WireClocks("wireclocks-coreir",c->Named("coreir.clkIn")));
  }
}

#endif //PASSES_HPP_
