#ifndef PASSES_COMMON_H_
#define PASSES_COMMON_H_

//Analysis passes
#include "analysis/hellomodule.h"
#include "analysis/printer.h"
#include "analysis/createinstancegraph.h"
#include "analysis/firrtl.h"
#include "analysis/verilog.h"
#include "coreir/passes/analysis/smtlib2.h"
#include "coreir/passes/analysis/smv.h"
#include "coreir/passes/analysis/verifyflatcoreirprims.h"
#include "analysis/coreirjson.h"
#include "analysis/magma.h"
#include "analysis/verifyconnectivity.h"
#include "analysis/verifyinputconnections.h"
#include "analysis/verifyflattenedtypes.h"
#include "analysis/createinstancemap.h"
#include "analysis/createcombview.h"

//Transform passes
#include "transform/flatten.h"
#include "transform/rungenerators.h"
#include "transform/flattentypes.h"
#include "transform/packconnections.h"
#include "transform/unpackconnections.h"
#include "transform/clockifyinterface.h"
#include "transform/removebulkconnections.h"
#include "transform/removepassthroughs.h"
#include "transform/removeunconnected.h"
#include "transform/registerinputs.h"
#include "transform/wireclocks.h"
#include "transform/cullgraph.h"

#include "transform/adddirected.h"
#include "transform/transform2combview.h"


//TODO Macrofy this
namespace CoreIR {
  void initializePasses(PassManager& pm) {
    Context* c = pm.getContext();
    //Analysis
    pm.addPass(new Passes::HelloModule());
    pm.addPass(new Passes::Printer());
    pm.addPass(new Passes::CreateInstanceGraph());
    pm.addPass(new Passes::CreateInstanceMap());
    pm.addPass(new Passes::Firrtl());
    pm.addPass(new Passes::CoreIRJson());
    pm.addPass(new Passes::Magma());
    pm.addPass(new Passes::Verilog());
    pm.addPass(new Passes::SmtLib2());
    pm.addPass(new Passes::SMV());
    pm.addPass(new Passes::VerifyFlatCoreirPrims());
    pm.addPass(new Passes::VerifyInputConnections());
    pm.addPass(new Passes::VerifyConnectivity(true,true));
    pm.addPass(new Passes::VerifyConnectivity(true,false));
    pm.addPass(new Passes::VerifyConnectivity(false,true));
    pm.addPass(new Passes::VerifyConnectivity(false,false));
    pm.addPass(new Passes::VerifyFlattenedTypes());
    pm.addPass(new Passes::CreateCombView());


    //Transform
    pm.addPass(new Passes::Flatten());
    pm.addPass(new Passes::RunGenerators());
    pm.addPass(new Passes::FlattenTypes());
    pm.addPass(new Passes::RemoveBulkConnections());
    pm.addPass(new Passes::RemovePassthroughs());
    pm.addPass(new Passes::RemoveUnconnected());
    pm.addPass(new Passes::WireClocks("wireclocks-coreir",c->Named("coreir.clkIn")));
    pm.addPass(new Passes::CullGraph());
    pm.addPass(new Passes::AddDirected());
    pm.addPass(new Passes::PackConnections());
    pm.addPass(new Passes::UnpackConnections());
    pm.addPass(new Passes::ClockifyInterface("clockifyinterface"));
    pm.addPass(new Passes::RegisterInputs("registerinputs"));
    pm.addPass(new Passes::Transform2CombView());
  }
}

#endif //PASSES_HPP_
