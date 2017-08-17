#ifndef HELLOA_HPP_
#define HELLOA_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class HelloA : public NamespacePass {
  std::string str = "DEADBEEF";
  public :
    static std::string ID;
    
    HelloA() : NamespacePass(ID,"Hello analysis",true) {}
    bool runOnNamespace(Namespace* ns) override;
    void releaseMemory() override {
      str = "DEAD";
    }
    string getString() { return str;}
};

}
}
#endif
