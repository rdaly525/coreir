#ifndef FLATTEN_HPP_
#define FLATTEN_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class Flatten : public InstanceGraphPass {
  public :
    static std::string ID;
    Flatten() : InstanceGraphPass(ID,"Flattens everything!") {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node);
};

}
}
#endif
