#ifndef HELLOA_HPP_
#define HELLOA_HPP_

#include "coreir.h"

namespace CoreIR {
namespace Passes {

class HelloA : public NamespacePass {
  std::string str;
  public :
    HelloA() : NamespacePass("helloa","Hello analysis",true) {}
    bool runOnNamespace(Namespace* ns);
    string getString() { return str;}
};

Pass* registerHelloA() {
  return new HelloA;
}

}
}
#endif
