#ifndef REGISTERINPUTSPASS_HPP_
#define REGISTERINPUTSPASS_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class RegisterInputs : public InstanceGraphPass {
  private :

  public :
  RegisterInputs(std::string name) : InstanceGraphPass(name, "Register all non-clock inputs.") {}
  bool runOnInstanceGraphNode(InstanceGraphNode& node);

};

}
}
#endif
