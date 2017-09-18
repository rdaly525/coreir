#ifndef COREIR_FIRRTL_HPP_
#define COREIR_FIRRTL_HPP_

#include "coreir.h"
#include <ostream>

namespace CoreIR {
namespace Passes {

class Firrtl : public InstanceGraphPass {
  std::unordered_map<Instantiable*,std::string> nameMap;
  std::vector<std::string> fmods;
  public :
    static std::string ID;
    Firrtl() : InstanceGraphPass(ID,"Creates Firrtl representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      addDependency("verifyconnectivity");
    }
    void writeToStream(std::ostream& os);
};

}
}
#endif
