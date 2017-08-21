#ifndef VERIFY_HPP_
#define VERIFY_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

  //TODO description
class WeakVerify : public ModulePass {
  public :
    static std::string ID;
    WeakVerify() : ModulePass(ID,"Verifies no multiple outputs to inputs",true) {}
    bool runOnModule(Module* m) override;
};

}
}
#endif
