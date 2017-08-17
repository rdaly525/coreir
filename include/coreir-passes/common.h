#ifndef PASSES_COMMON_H_
#define PASSES_COMMON_H_

//#include "matchandreplace.hpp"
//#include "flattenallpass.hpp"
//#include "runallgeneratorspass.hpp"
//#include "flattenconnections.hpp"
//#include "printpass.hpp"
//#include "wireclockpass.hpp"

//Analysis passes
#include "analysis/helloa.h"

//Transform passes
#include "transform/hellot.h"
#include "transform/wireclockpass.h"


#define ADDPASS(name) \
  pm.addPass(Passes::register ## name());

namespace CoreIR {
  void initializePasses(PassManager& pm) {
    ADDPASS(HelloA)
    ADDPASS(HelloT)
  }
}


#endif //PASSES_HPP_
