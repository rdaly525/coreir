#ifndef WIRECLOCKPASS_HPP_
#define WIRECLOCKPASS_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class WireClocks : public ModulePass {
  private :
    Type* clockType; 
  public :

    WireClocks(std::string name, Type* clockType) : ModulePass(name,"Wire any module with clocktype"), clockType(clockType) {}
    bool runOnModule(Module* m);
};

}
}
#endif
