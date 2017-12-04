#pragma once

#include "coreir/ir/value.h"
#include "coreir/ir/wireable.h"

#include "coreir/simulator/op_graph.h"
#include "coreir/simulator/print_c.h"
#include "coreir/simulator/utils.h"

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


  static std::string lastClkVarName(InstanceValue& clk) {
    return cVar("(state->", clk, "_last)");
  }

  static std::string clkVarName(InstanceValue& clk) {
    return cVar("(state->", clk, ")");
  }

  static std::string outputVarName(CoreIR::Wireable& outSel) {
    return cVar("(state->", outSel, ")");
  }

  static std::string outputVarName(const InstanceValue& val) {
    return cVar("(state->", val, ")");
  }

  static inline CoreIR::Select* baseSelect(CoreIR::Select* const sel) {
    if (!isSelect(sel->getParent())) {
      return sel;
    }

    return baseSelect(toSelect(sel->getParent()));
  }

  class CustomStructLayout : public LayoutPolicy {
  public:
    std::vector<std::pair<CoreIR::Type*, std::string> > varDecls;
    std::set<std::string> allocatedAlready;

    CoreIR::Context* c;

    CustomStructLayout(CoreIR::Context* const c_) : c(c_) {}

    void forceAdjacent(const std::vector<std::string>& vars) {
      std::vector<unsigned> adjacentInds;
      for (auto& v : vars) {
        for (unsigned i = 0; i < varDecls.size(); i++) {
          auto& elem = varDecls[i];
          if (elem.second == v) {
            adjacentInds.push_back(i);
            break;
          }
        }
      }

      int oldSize = varDecls.size();

      std::vector<std::pair<Type*, std::string> > adj;
      for (auto& ind : adjacentInds) {
        adj.push_back(varDecls[ind]);
      }

      std::vector<std::pair<Type*, std::string> > others;
      for (uint i = 0; i < varDecls.size(); i++) {
        if (!elem(i, adjacentInds)) {
          others.push_back(varDecls[i]);
        }
      }

      varDecls = others;
      concat(varDecls, adj);

      assert(varDecls.size() == ((unsigned) oldSize));
    }

    std::string lastClkVarName(InstanceValue& clk) {
      varDecls.push_back({clk.getWire()->getType(), cVar("", clk, "_last")});
      return CoreIR::lastClkVarName(clk);
    }

    std::string clkVarName(InstanceValue& clk) {
      varDecls.push_back({clk.getWire()->getType(), cVar(clk)});
      return CoreIR::clkVarName(clk);
    }

    std::string selectName(CoreIR::Select* sel) {
      Select* baseSel = baseSelect(toSelect(sel));

      if (!elem(cVar(baseSel), allocatedAlready)) {
        varDecls.push_back({baseSel->getType(), cVar(baseSel)});
        allocatedAlready.insert(cVar(baseSel));
      }

      return CoreIR::outputVarName(sel);
    }

    std::string outputVarName(CoreIR::Wireable& val) {

      if (isSelect(val)) {
        return selectName(toSelect(&val));
      }

      assert(isInstance(&val));

      if (isRegisterInstance(&val)) {

        Select* sel = val.sel("out");
        if (!elem(cVar(val), allocatedAlready)) {
          varDecls.push_back({sel->getType(), cVar(val)});
          allocatedAlready.insert(cVar(val));
        }

        return CoreIR::outputVarName(val);
      } else if (isMemoryInstance(&val)) {

        if (!elem(cVar(val), allocatedAlready)) {
          Instance* is = toInstance(&val);

          Values args = is->getModuleRef()->getGenArgs();

          auto wArg = args["width"];
          auto dArg = args["depth"];
        
          uint width = wArg->get<int>();
          uint depth = dArg->get<int>();
          Type* elemType = c->Array(depth, c->Array(width, c->BitIn()));

          varDecls.push_back({elemType, cVar(val)});
          allocatedAlready.insert(cVar(val));
        }

        return CoreIR::outputVarName(val);
      }

      assert(false);
    }

    std::string outputVarName(const InstanceValue& val) {
      std::cout << "Creating output for " << val.getWire()->toString() << std::endl;

      return selectName(val.getWire());
    }
    
  };


  
}
