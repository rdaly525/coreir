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

  typedef std::pair<CoreIR::Type*, std::string> VarDecl;

  class CustomStructLayout : public LayoutPolicy {

    std::vector<std::vector<VarDecl> > adjacentGroups;
    std::vector<VarDecl> varDecls;

  public:
    std::set<std::string> allocatedAlready;
    CoreIR::Context* c;

    CustomStructLayout(CoreIR::Context* const c_) : c(c_) {}

    std::vector<std::pair<CoreIR::Type*, std::string> > getVarDecls() const {
      return varDecls;
    }

    bool adjacent(const std::string& a,
                  const std::string& b,
                  const std::vector<VarDecl>& decls) {
      assert(decls.size() >= 2);

      for (uint i = 0; i < decls.size() - 1; i++) {
        if ((decls[i].second == a) &&
            (decls[i + 1].second == b)) {
          return true;
        }
      }

      return false;
    }

    bool canMerge(const std::string& a,
                  const std::string& b) {
      if (adjacentGroups.size() == 0) {
        return true;
      }

      uint aGroup = 0;
      uint bGroup = 0;
      for (uint i = 0; i < adjacentGroups.size(); i++) {
        auto valGroup = adjacentGroups[i];
        for (uint j = 0; j < valGroup.size(); j++) {
          if (valGroup[j].second == a) {
            aGroup = i;
          }

          if (valGroup[j].second == b) {
            bGroup = i;
          }

        }
      }

      assert(aGroup < adjacentGroups.size());
      assert(bGroup < adjacentGroups.size());

      if ((aGroup == bGroup) && (adjacent(a, b, adjacentGroups[aGroup]))) {
        return true;
      }

      if ((adjacentGroups[aGroup].back().second == a) &&
          (adjacentGroups[bGroup].front().second == b)) {
        return true;
      }

      return false;
    }

    void forceAdjacent(const std::vector<std::string>& vars) {
      assert(vars.size() > 1);

      for (uint i = 0; i < vars.size() - 1; i++) {
        std::string a = vars[i];
        std::string b = vars[i + 1];

        if (!canMerge(a, b)) {
          std::cout << "ERROR: Cannot merge " << a << " and " << b << std::endl;
          assert(false);
        }
      }

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

      adjacentGroups.push_back(adj);
      varDecls = others;
      concat(varDecls, adj);

      ASSERT(varDecls.size() == ((unsigned) oldSize), "oldsize is " + std::to_string(oldSize));
    }

    std::string lastClkVarName(InstanceValue& clk) {
      if (!elem(cVar("", clk, "_last"), allocatedAlready)) {
        varDecls.push_back({clk.getWire()->getType(), cVar("", clk, "_last")});
        adjacentGroups.push_back({{clk.getWire()->getType(), cVar("", clk, "_last")}});
        allocatedAlready.insert(cVar("", clk, "_last"));
      }

      return CoreIR::lastClkVarName(clk);
    }

    std::string clkVarName(InstanceValue& clk) {
      if (!elem(cVar(clk), allocatedAlready)) {
        varDecls.push_back({clk.getWire()->getType(), cVar(clk)});
        adjacentGroups.push_back({{clk.getWire()->getType(), cVar(clk)}});
        allocatedAlready.insert(cVar(clk));
      }

      return CoreIR::clkVarName(clk);
    }

    std::string selectName(CoreIR::Select* sel) {
      Select* baseSel = baseSelect(toSelect(sel));

      if (!elem(cVar(baseSel), allocatedAlready)) {
        varDecls.push_back({baseSel->getType(), cVar(baseSel)});
        adjacentGroups.push_back({{baseSel->getType(), cVar(baseSel)}});
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
          adjacentGroups.push_back({{sel->getType(), cVar(val)}});
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
          adjacentGroups.push_back({{elemType, cVar(val)}});
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
