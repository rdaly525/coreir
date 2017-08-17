#ifndef VERILOG_HPP_
#define VERILOG_HPP_

#include "coreir.h"
#include <ostream>

using namespace CoreIR;
namespace CoreIR {
namespace Passes {

class Verilog : public InstanceGraphPass {
  unordered_map<Instantiable*,string> nameMap;
  vector<string> vmods;
  public :
    static std::string ID;
    Verilog() : InstanceGraphPass(ID,"Creates Verilog representation of IR",true) {}
    bool runOnInstanceGraphNode(InstanceGraphNode& node) override;
    void writeToStream(std::ostream& os);
};

}
}
#endif
