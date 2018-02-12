#ifndef COREIR_PACKBITCONSTANTS_HPP_
#define COREIR_PACKBITCONSTANTS_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

//This will add directed connection metadata to modules
class PackBitConstants : public ModulePass {
  
  public:
    static std::string ID;
    PackBitConstants() : ModulePass(ID, "Convert lists of corebit.const into coreir.const. E.G. convert 32 1 bit constants into one 32 bit constant.") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif
