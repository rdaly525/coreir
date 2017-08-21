#ifndef FIRRTL_HPP_
#define FIRRTL_HPP_

#include "coreir.h"
#include <ostream>

using namespace CoreIR;
namespace CoreIR {
namespace Passes {

class Firrtl : public InstanceGraphPass {
  unordered_map<Instantiable*,string> nameMap;
  vector<string> fmods;
  public :
    static std::string ID;
    Firrtl() : InstanceGraphPass(ID,"Creates Firrtl representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      addDependency("strongverify");
    }
    void writeToStream(std::ostream& os);
};

}
}
#endif
