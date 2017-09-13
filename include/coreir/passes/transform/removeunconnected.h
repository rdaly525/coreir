#ifndef REMOVEUNCONNECTED_HPP_
#define REMOVEUNCONNECTED_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class RemoveUnconnected : public InstancePass {
  public :
    static std::string ID;
    RemoveUnconnected() : InstancePass(ID,"Removes unconnected Instances") {}
    bool runOnInstance(Instance* i) override;
};

}
}
#endif
