#ifndef REMOVEPASSTHROUGHS_H_
#define REMOVEPASSTHROUGHS_H_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

  class RemovePassthroughs : public InstanceVisitorPass {
  public :
    static std::string ID;
  RemovePassthroughs(Context* c) : InstanceVisitorPass(ID,"Inlines all passthroughs"), c(c) {}
    void setVisitorInfo() override;
  private: 
    Context* c;
  };


}
}

#endif
