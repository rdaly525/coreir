#ifndef REMOVEWIRES_H_
#define REMOVEWIRES_H_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

  class RemoveWires : public InstanceVisitorPass {
  public :
    static std::string ID;
  RemoveWires() : InstanceVisitorPass(ID,"Inlines all wires") {}
    void setVisitorInfo() override;
  };


}
}

#endif
