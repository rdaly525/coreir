#ifndef RUNALLGENERATORSPASS_HPP_
#define RUNALLGENERATORSPASS_HPP_

#include "coreir.h"

using namespace CoreIR;

// This will recusrively run all the generators and replace module definitions
// For every instance, if it is a generator, it 

class RunAllGeneratorsPass : public NamespacePass {
  public :
    RunAllGeneratorsPass() : NamespacePass() {}
    bool runOnNamespace(Namespace* ns);
};


#endif
