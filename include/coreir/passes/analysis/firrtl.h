#ifndef FIRRTL_HPP_
#define FIRRTL_HPP_

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
      addDependency("verifyfullyconnected");
    }
    void writeToStream(std::ostream& os);
};

}
}
#endif
