#ifndef COREIR_CULLGRAPH_HPP_
#define COREIR_CULLGRAPH_HPP_

#include "coreir.h"
// This will recusrively run all the generators and replace module definitions
// For every instance, if it is a generator, it 

namespace CoreIR {
namespace Passes {


class CullGraph : public ContextPass {
  bool nocoreir;
  public :
    static std::string ID;
    CullGraph(bool nocoreir) : ContextPass(ID + (nocoreir ? "" : "-withcoreir"),"Runs all generators"), nocoreir(nocoreir) {}
    bool runOnContext(Context* c);
};

}
}

#endif
