#ifndef COREIR_CLOCKIFYINTERFACE_HPP_
#define COREIR_CLOCKIFYINTERFACE_HPP_

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

//This will add directed connection metadata to modules
  class ClockifyInterface : public InstanceGraphPass {
  
  public:

    ClockifyInterface(std::string name) : InstanceGraphPass(name, "Convert any BitIn fields in the interface that are only used as clocks into fields with named type coreir.clkIn") {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
};

}
}

#endif
