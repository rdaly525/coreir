#ifndef REMOVEPASSTHROUGHS_H_
#define REMOVEPASSTHROUGHS_H_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

  class RemovePassthroughs : public InstanceVisitorPass {
  public :
    static std::string ID;
  RemovePassthroughs() : InstanceVisitorPass(ID,"Inlines all passthroughs") {}
    void setVisitorInfo() override;
  };


}
}

#endif
