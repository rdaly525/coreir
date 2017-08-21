#ifndef VERILOG_HPP_
#define VERILOG_HPP_

#include "coreir.h"
#include <ostream>
#include "vmodule.hpp"

using namespace CoreIR;
namespace CoreIR {
namespace Passes {

class Verilog : public InstanceGraphPass {
  unordered_map<Instantiable*,VModule*> modMap;
  unordered_set<Instantiable*> external;
  public :
    static std::string ID;
    Verilog() : InstanceGraphPass(ID,"Creates Verilog representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void setAnalysisInfo() override {
      addDependency("strongverify");
      addDependency("verifyflattenedtypes");
    }
    
    void writeToStream(std::ostream& os);
};

}
}
#endif
