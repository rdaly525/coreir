#ifndef COREIRJSON_HPP_
#define COREIRJSON_HPP_

#include "coreir.h"
#include <map>

namespace CoreIR {
namespace Passes {

class CoreIRJson : public NamespacePass {

  map<string,string> nsMap;
  public :
    static std::string ID;
    CoreIRJson() : NamespacePass(ID,"Creates a json of the coreir",true) {}
    bool runOnNamespace(Namespace* ns) override;
    void writeToStream(std::ostream& os,string topRef);
};

}
}
#endif
