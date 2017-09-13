#ifndef VERIFY_HPP_
#define VERIFY_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

//Verifies that All input connections are driven by exactly one source
class VerifyInputConnections : public ModulePass {
  public :
    static std::string ID;
    VerifyInputConnections() : ModulePass(ID,"Verifies no multiple outputs to inputs",true) {}
    bool runOnModule(Module* m) override;
};

}
}
#endif
