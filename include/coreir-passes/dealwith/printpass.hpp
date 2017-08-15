#ifndef PRINTPASS_HPP_
#define PRINTPASS_HPP_

#include "coreir.h"

using namespace CoreIR;

// This will recusrively run all the generators and replace module definitions
// For every instance, if it is a generator, it 

class PrintPass : public NamespacePass {
  public :
    PrintPass() : NamespacePass() {}
    bool runOnNamespace(Namespace* ns);
};


#endif
