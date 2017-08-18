#ifndef VERIFY_HPP_
#define VERIFY_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

//This will Verify that all modules 
class Verify : public ModulePass {
  public :
    static std::string ID;
    Verify() : ModulePass(ID,"Verification",true) {}
    bool runOnModule(Module* m) override;
};

}
}
#endif
