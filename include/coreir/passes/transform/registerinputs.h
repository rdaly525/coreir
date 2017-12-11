#ifndef WIRECLOCKPORTPASS_HPP_
#define WIRECLOCKPORTPASS_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class Registerinputs : public InstanceGraphPass {
  private :
    Type* clockType; 
  public :
  Registerinputs(std::string name) : InstanceGraphPass(name, "Register all non-clock inputs.") {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node);

};

}
}
#endif
