#ifndef WIRECLOCKPASS_HPP_
#define WIRECLOCKPASS_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class WireClockPass : public ModulePass {
  private :
    Type* clockType; 
  public :
    static std::string ID;
    WireClockPass(Type* clockType) : ModulePass(ID,"Wire any module with clocktype"), clockType(clockType) {}
    bool runOnModule(Module* m);
};

//Pass* registeWireClockPass();


}
}
#endif
