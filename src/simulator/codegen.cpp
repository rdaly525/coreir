#include "coreir/simulator/codegen.h"

#include "coreir/ir/value.h"

#include "coreir/simulator/print_c.h"

using namespace std;

namespace CoreIR {

  bool underlyingTypeIsClkIn(Type& tp) {
    if (isClkIn(tp)) {
      return true;
    }

    if (isArray(tp)) {
      ArrayType& tarr = toArray(tp);
      return underlyingTypeIsClkIn(*(tarr.getElemType()));
    }

    return false;

  }

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
    string res = "struct __attribute__((packed, aligned(32))) circuit_state {\n";

    auto decls = mc.structLayout;

    concat(decls, threadSharedVariableDecls(mc.g));
    
    // sort_lt(decls, [](const pair<Type*, string>& tpp) {
    //     return tpp.second;
    //   });

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



  std::vector<std::pair<CoreIR::Type*, std::string> >
  simMemoryInputs(Module& mod) {
    vector<pair<Type*, string>> declStrs;
    
    // Add register inputs
    for (auto& inst : mod.getDef()->getInstances()) {
      if (isMemoryInstance(inst.second)) {
        cout << "Adding memory instance" << endl;
        Instance* is = inst.second;

        Context* c = mod.getDef()->getContext();

        Values args = is->getModuleRef()->getGenArgs();

        auto wArg = args["width"];
        auto dArg = args["depth"];
        
        uint width = wArg->get<int>(); //16;
        uint depth = dArg->get<int>();
        Type* elemType = c->Array(depth, c->Array(width, c->BitIn()));
        declStrs.push_back({elemType, is->toString()});

      }
    }

    return declStrs;
  }  

  std::vector<std::pair<CoreIR::Type*, std::string> >
  simRegisterInputs(Module& mod) {

    vector<pair<Type*, string>> declStrs;
    
    // Add register inputs
    for (auto& inst : mod.getDef()->getInstances()) {
      if (isRegisterInstance(inst.second)) {
        Instance* is = inst.second;

        Select* in = is->sel("in");
        Type* itp = in->getType();

        string regName = is->getInstname();

        declStrs.push_back({itp, cVar(*is)});
        
      }
    }

    return declStrs;
    
  }

  std::vector<std::pair<CoreIR::Type*, std::string> >
  sortedSimArgumentPairs(Module& mod) {

    Type* tp = mod.getType();

    assert(tp->getKind() == Type::TK_Record);

    RecordType* modRec = static_cast<RecordType*>(tp);
    vector<pair<Type*, string>> declStrs;

    for (auto& name_type_pair : modRec->getRecord()) {
      Type* tp = name_type_pair.second;

      if (tp->isInput()) {
        if (!underlyingTypeIsClkIn(*tp)) {
          declStrs.push_back({tp, "self_" + name_type_pair.first});
        } else {
          declStrs.push_back({tp, "self_" + name_type_pair.first});
          declStrs.push_back({tp, "self_" + name_type_pair.first + "_last"});

        }
      } else {
        assert(tp->isOutput());

        declStrs.push_back({tp, "self_" + name_type_pair.first});

      }
    }

    concat(declStrs, simRegisterInputs(mod));
    concat(declStrs, simMemoryInputs(mod));

    return declStrs;
  }

  std::vector<string> sortedSimArgumentList(Module& mod,
                                            const NGraph& g) {

    auto decls = sortedSimArgumentPairs(mod);

    concat(decls, threadSharedVariableDecls(g));
    
    sort_lt(decls, [](const pair<Type*, string>& tpp) {
        return tpp.second;
      });

    vector<string> declStrs;
    for (auto declPair :  decls) {
      declStrs.push_back(cArrayTypeDecl(*(declPair.first), declPair.second));
    }

    return declStrs;
  }

}
