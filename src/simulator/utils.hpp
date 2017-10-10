#pragma once

#include "coreir.h"

#include "algorithm.hpp"

namespace CoreIR {

  static inline bool isSelect(CoreIR::Wireable* fst) {
    return fst->getKind() == CoreIR::Wireable::WK_Select;
  }

  static inline CoreIR::Select* toSelect(CoreIR::Wireable* w) {
    assert(isSelect(w));
    return static_cast<CoreIR::Select*>(w);
  }

  static inline bool isSelect(const CoreIR::Wireable& fst) {
    return fst.getKind() == CoreIR::Wireable::WK_Select;
  }

  static inline CoreIR::Select& toSelect(CoreIR::Wireable& fst) {
    assert(isSelect(fst));
    return static_cast<CoreIR::Select&>(fst);
  }

  static inline bool fromSelf(CoreIR::Select* w) {
    CoreIR::Wireable* parent = w->getParent();
    if (isSelect(parent)) {
      return fromSelf(toSelect(parent));
    }

    return parent->toString() == "self";
  }

  
  static inline bool isInstance(CoreIR::Wireable* fst) {
    return fst->getKind() == CoreIR::Wireable::WK_Instance;
  }

  static inline bool isInterface(CoreIR::Wireable* fst) {
    return fst->getKind() == CoreIR::Wireable::WK_Interface;
  }
  
  static inline CoreIR::Instance* toInstance(CoreIR::Wireable* fst) {
    assert(isInstance(fst));
    return static_cast<CoreIR::Instance*>(fst);
  }

  static inline bool isRegisterInstance(CoreIR::Wireable* fst) {
    //cout << "checking isRegisterInstance " << fst->toString() << endl;

    if (!isInstance(fst)) {
      return false;
    }

    //cout << "Is instance" << endl;

    CoreIR::Instance* inst = toInstance(fst);

    auto genRef = inst->getGeneratorRef();

    //cout << "genRef is null ? " << (genRef == nullptr) << endl;

    if (genRef == nullptr) {
      //std::cout << "ERROR: genRef is null for " << fst->toString() << std::endl;

      Module* modRef = inst->getModuleRef();

      //std::cout << "Module ref is null ? " << (modRef == nullptr) << std::endl;

      assert(modRef != nullptr);

      //cout << "Module ref name = " << modRef->getName() << endl;      

      return modRef->getName() == "reg";
    }

    std::string genRefName = genRef->getName();

    return genRefName == "reg";
  }

  static inline bool isMemoryInstance(CoreIR::Wireable* fst) {
    if (!isInstance(fst)) {
      return false;
    }

    CoreIR::Instance* inst = toInstance(fst);

    auto genRef = inst->getGeneratorRef();

    if (genRef == nullptr) {
      Module* modRef = inst->getModuleRef();

      assert(modRef != nullptr);

      return modRef->getName() == "mem";
    }

    std::string genRefName = genRef->getName();

    return genRefName == "mem";
  }
  
  static inline bool isNamedType(CoreIR::Type& t, const std::string& name) {
    if (t.getKind() != CoreIR::Type::TK_Named) {
      return false;
    }

    CoreIR::NamedType& nt = static_cast<CoreIR::NamedType&>(t);
    return nt.getName() == name;

  }

  
  static inline bool isArray(CoreIR::Type& t) {
    return t.getKind() == CoreIR::Type::TK_Array;
  }

  static inline bool isClkIn(CoreIR::Type& t) {
    return isNamedType(t, "clkIn");
  }

  
  bool isBitArray(CoreIR::Type& t);
  bool isBitArrayOfLength(CoreIR::Type& t, const uint len);
  bool isBitArrayOfLengthLEQ(CoreIR::Type& t, const uint len);
  bool isPrimitiveType(CoreIR::Type& t);

  std::unordered_map<std::string, CoreIR::Wireable*>
  getOutputSelects(CoreIR::Wireable* inst);

  std::unordered_map<std::string, CoreIR::Wireable*>
  getInputSelects(CoreIR::Wireable* inst);

  bool recordTypeHasField(const std::string& fieldName, CoreIR::Type* t);

  std::string commaSepList(std::vector<std::string>& declStrs);

  static inline std::string selectInfoString(CoreIR::Wireable* w) {
    assert(isSelect(w));

    CoreIR::Select* s = static_cast<CoreIR::Select*>(w);
    std::string ss = s->getSelStr();

    return ss + " " + s->getType()->toString();
  }

  uint typeWidth(CoreIR::Type& tp);

  uint containerTypeWidth(CoreIR::Type& tp);

  bool standardWidth(CoreIR::Type& tp);

  static inline CoreIR::ArrayType& toArray(CoreIR::Type& tp) {
    assert(isArray(tp));

    return static_cast<CoreIR::ArrayType&>(tp);
  }


  bool connectionIsOrdered(const CoreIR::Connection& connection);

  std::string getOpName(CoreIR::Instance& inst);

  static inline
  std::string getInstanceName(Instance& w) {
    auto g = w.getGeneratorRef();

    if (g == nullptr) {
      auto m = w.getModuleRef();

      assert(m != nullptr);

      return m->getName();
    }

    return g->getName();
  }

  static inline Generator* getGeneratorRef(Instance& w) {
    auto g = w.getGeneratorRef();

    assert(g != nullptr);

    return g;
  }

  static inline bool isDASHR(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    return genRefName == "ashr";
  }

  static inline bool isShiftOp(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> bitwiseOps{"shl", "lshr", "ashr"};
    return elem(genRefName, bitwiseOps);
  }

  static inline bool isSDivOrRem(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> bitwiseOps{"sdiv", "srem"};
    return elem(genRefName, bitwiseOps);
  }
  
  static inline bool isUDivOrRem(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> bitwiseOps{"udiv", "urem"};
    return elem(genRefName, bitwiseOps);
  }

  static inline bool isBitwiseOp(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> bitwiseOps{"not", "and", "or", "xor", "bitor", "bitand", "bitxor"};
    return elem(genRefName, bitwiseOps);
  }

  static inline bool isSignInvariantOp(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> siOps{"add", "sub", "mul", "eq"};
    return elem(genRefName, siOps);
  }

  static inline bool isAddOrSub(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> siOps{"add", "sub"};
    return elem(genRefName, siOps);
  }
  
  static inline bool isUnsignedCmp(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> siOps{"ult", "ugt", "ule", "uge"};
    return elem(genRefName, siOps);
  }

  static inline bool isSignedCmp(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> siOps{"slt", "sgt", "sle", "sge"};
    return elem(genRefName, siOps);
  }
  
}
