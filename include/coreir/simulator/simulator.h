#pragma once

#include "coreir/simulator/codegen.h"
#include "coreir/simulator/multithreading.h"

namespace CoreIR {

  class LayoutPolicy {
  protected:

    bool readRegsDirectly;

  public:
    LayoutPolicy() : readRegsDirectly(false) {}

    virtual ~LayoutPolicy() {}

    virtual void setReadRegsDirectly(const bool newVal) {
      readRegsDirectly = newVal;
    }

    virtual bool getReadRegsDirectly() const {
      return readRegsDirectly;
    }
    
    virtual std::string lastClkVarName(InstanceValue& clk) const = 0;

    virtual std::string clkVarName(InstanceValue& clk) const = 0;

    virtual std::string outputVarName(CoreIR::Wireable& outSel) const = 0;

    virtual std::string outputVarName(const InstanceValue& val) const = 0;

  };

  std::string
  printSimFunctionBody(const std::deque<vdisc>& topo_order,
                       NGraph& g,
                       Module& mod,
                       const int threadNo,
                       const LayoutPolicy& layoutPolicy);

  std::string printCode(const ModuleCode& mc);

  ModuleCode buildCode(const std::deque<vdisc>& topoOrder,
                       NGraph& g,
                       CoreIR::Module* mod,
                       const std::string& baseName);

  std::string printDecl(const ModuleCode& mc);

  std::vector<std::pair<CoreIR::Type*, std::string> >
  sortedSimArgumentPairs(Module& mod);


  ThreadGraph buildThreadGraph(const NGraph& opG);

  std::string seMacroDef();
  std::string maskMacroDef();

}
