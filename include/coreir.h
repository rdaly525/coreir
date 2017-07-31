#ifndef COREIR_H_
#define COREIR_H_



//TODO I should actually move over all the hpp files into include directly
//Also should create coreir/ to put all these files in to be consistent
#include "../src/ir/context.hpp"
#include "../src/ir/directedview.hpp"
#include "passmanager.h"
#include "passes.h"
#include "instancegraph.h"

#include "../src/ir/typegenlang/typegenlang.hpp"
#include "../src/ir/typegenlang/common.hpp"
#include "../src/ir/typegenlang/vtype.hpp"

namespace CoreIR {
//extra helper functions

//Inlines the instance
  bool inlineInstance(Instance*);
  Instance* addPassthrough(Wireable* w,std::string instname);
}

#endif //COREIR_H_
