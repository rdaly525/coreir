#ifndef WIRECLOCKPASS_HPP_
#define WIRECLOCKPASS_HPP_

#include "coreir.h"

using namespace CoreIR;

class WireClockPass : public ModulePass {
  private :
    Type* clockType; 
  public :
    WireClockPass(Type* clockType) : ModulePass(), clockType(clockType) {}
    bool runOnModule(Module* m);
};

#endif
