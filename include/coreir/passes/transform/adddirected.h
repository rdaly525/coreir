#ifndef COREIR_ADDDIRECTED_HPP_
#define COREIR_ADDDIRECTED_HPP_

#include "coreir.h"

//Define the analysis passes in CoreIR::Passes
namespace CoreIR {
namespace Passes {

//This will add directed connection metadata to modules
class AddDirected : public ModulePass {
  
  public:
    static std::string ID;
    AddDirected() : ModulePass(ID,"Descritpion Blah Blah") {}
    bool runOnModule(Module* m) override;
};

}
}

#endif
