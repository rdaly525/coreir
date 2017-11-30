#include "coreir/simulator/codegen.h"

#include "coreir/simulator/print_c.h"

using namespace std;

namespace CoreIR {

  std::vector<std::pair<CoreIR::Type*, std::string> >
  threadSharedVariableDecls(const NGraph& g) {
    vector<pair<Type*, string>> declStrs;

    for (auto& vd : g.getVerts()) {
      WireNode wd = getNode( g, vd);
      Wireable* w = wd.getWire();

      if (isThreadShared(vd, g)) {
        for (auto inSel : getOutputSelects(w)) {
          Select* in = toSelect(inSel.second);

          if (!fromSelfInterface(in)) {
            if (!arrayAccess(in)) {

              if (!wd.isSequential) {

                declStrs.push_back({in->getType(), cVar(*in)});

              }
            }
          }
        }
      }
    }

    return declStrs;
  }

  std::string printEvalStruct(const ModuleCode& mc) {
    string res = "struct circuit_state {\n";

    auto decls = mc.structLayout;

    concat(decls, threadSharedVariableDecls(mc.g));
    
    sort_lt(decls, [](const pair<Type*, string>& tpp) {
        return tpp.second;
      });

    vector<string> declStrs;
    for (auto declPair :  decls) {
      declStrs.push_back(cArrayTypeDecl(*(declPair.first), declPair.second));
    }

    for (auto& dstr : declStrs) {
      res += "\t" + dstr + ";\n";
    }
    
    res += "};\n\n";

    return res;
  }  

}
