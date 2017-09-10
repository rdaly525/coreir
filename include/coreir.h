#ifndef COREIR_H_
#define COREIR_H_



//TODO I should actually move over all the hpp files into include directly
//Also should create coreir/ to put all these files in to be consistent
#include "../src/ir/context.hpp"
#include "../src/ir/directedview.hpp"
#include "coreir-passmanager.h"
#include "coreir-passes.h"
#include "coreir-instancegraph.h"


namespace CoreIR {
//extra helper functions

//Inlines the instance
  bool inlineInstance(Instance*);
  Instance* addPassthrough(Wireable* w,std::string instname);
}

#endif //COREIR_H_
