#ifndef PASSES_COMMON_H_
#define PASSES_COMMON_H_

//#include "matchandreplace.hpp"
//#include "flattenallpass.hpp"
//#include "runallgeneratorspass.hpp"
//
//#include "flattenconnections.hpp"
//
//#include "printpass.hpp"

//Analysis passes
#include "analysis/helloa.h"

//Transform passes
#include "transform/hellot.h"


namespace CoreIR {
  void initializePasses(PassManager& pm) {
    pm.addPass(Passes::registerHelloA());


    pm.addPass(Passes::registerHelloT());
  }
}


#endif //PASSES_HPP_
