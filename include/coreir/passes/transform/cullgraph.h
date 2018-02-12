#ifndef COREIR_CULLGRAPH_HPP_
#define COREIR_CULLGRAPH_HPP_

#include "coreir.h"
// This will recusrively run all the generators and replace module definitions
// For every instance, if it is a generator, it 

namespace CoreIR {
namespace Passes {


class CullGraph : public ContextPass {
  public :
    static std::string ID;
    CullGraph() : ContextPass(ID,"Runs all generators") {}
    bool runOnContext(Context* c);
};

}
}

#endif
