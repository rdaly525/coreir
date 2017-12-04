#pragma once

namespace CoreIR {

  class LayoutPolicy {
  protected:

    bool readRegsDirectly;

  public:
    LayoutPolicy() : readRegsDirectly(false) {}

    virtual ~LayoutPolicy() {}

    virtual void forceAdjacent(const std::vector<std::string>& vars) {
      assert(false);
    }
    
    virtual void setReadRegsDirectly(const bool newVal) {
      readRegsDirectly = newVal;
    }

    virtual bool getReadRegsDirectly() const {
      return readRegsDirectly;
    }
    
    virtual std::string lastClkVarName(InstanceValue& clk) = 0;

    virtual std::string clkVarName(InstanceValue& clk) = 0;

    virtual std::string outputVarName(CoreIR::Wireable& outSel) = 0;

    virtual std::string outputVarName(const InstanceValue& val) = 0;

  };

  
}
