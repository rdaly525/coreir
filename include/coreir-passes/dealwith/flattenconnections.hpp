#ifndef FLATTENCONNECTIONS_HPP_
#define FLATTENCONNECTIONS_HPP_

#include "coreir.h"

using namespace CoreIR;

//This should change connections to only connect to bits or Arrays of bits
class FlattenConnections : public ModulePass {
  public :
    FlattenConnections() : ModulePass() {}
    bool runOnModule(Module* m);
    void print();
};


#endif
