#pragma once

#include "coreir.h"

namespace CoreIR {

  static inline bool isSelect(CoreIR::Wireable* fst) {
    return fst->getKind() == CoreIR::Wireable::WK_Select;
  }

  static inline bool isSelect(const CoreIR::Wireable& fst) {
    return fst.getKind() == CoreIR::Wireable::WK_Select;
  }

  static inline CoreIR::Select& toSelect(CoreIR::Wireable& fst) {
    assert(isSelect(fst));
    return static_cast<CoreIR::Select&>(fst);
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

    string genRefName = genRef->getName();

    return genRefName == "reg";
  }
  
  static inline std::string cVar(CoreIR::Wireable& w) {
    if (isSelect(w)) {
      CoreIR::Select& s = toSelect(w);
      if (CoreIR::isNumber(s.getSelStr())) {
	return cVar(*(s.getParent())) + "[" + s.getSelStr() + "]";
      } else {
	return cVar(*(s.getParent())) + "_" + s.getSelStr();
      }
    } else {
      return w.toString();
    }
  }

  static inline std::string cVar(CoreIR::Wireable& w, const std::string& suffix) {
    cout << "cvar for " << w.toString() << " with suffix = " << suffix << endl;
    if (isSelect(w)) {
      CoreIR::Select& s = toSelect(w);
      if (CoreIR::isNumber(s.getSelStr())) {
	//cout << "select is number" << endl;
	return cVar(*(s.getParent()), suffix) + "[" + s.getSelStr() + "]";
      } else {
	//cout << "Select is not number" << endl;
	return cVar(*(s.getParent())) + "_" + s.getSelStr() + suffix;
      }
    } else {
      //cout << "Not a select" << endl;
      return w.toString() + suffix;
    }
  }

  static inline std::string cVar(const std::string& prefix,
				 CoreIR::Wireable& w,
				 const std::string& suffix) {

    if (isSelect(w)) {
      CoreIR::Select& s = toSelect(w);
      if (CoreIR::isNumber(s.getSelStr())) {

	return cVar(prefix, *(s.getParent()), suffix) + "[" + s.getSelStr() + "]";

      } else {

	return prefix + cVar(*(s.getParent())) + "_" + s.getSelStr() + suffix;
      }
    } else {

      return prefix + w.toString() + suffix;
    }
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

  unordered_map<string, CoreIR::Wireable*>
  getOutputSelects(CoreIR::Wireable* inst);

  unordered_map<string, CoreIR::Wireable*>
  getInputSelects(CoreIR::Wireable* inst);

  bool recordTypeHasField(const std::string& fieldName, CoreIR::Type* t);

  std::string commaSepList(std::vector<std::string>& declStrs);

  static inline std::string selectInfoString(CoreIR::Wireable* w) {
    assert(isSelect(w));

    CoreIR::Select* s = static_cast<CoreIR::Select*>(w);
    std::string ss = s->getSelStr();

    return ss + " " + s->getType()->toString();
  }

  static inline CoreIR::Select* toSelect(CoreIR::Wireable* w) {
    assert(isSelect(w));
    return static_cast<CoreIR::Select*>(w);
  }

  static inline bool fromSelf(CoreIR::Select* w) {
    CoreIR::Wireable* parent = w->getParent();
    if (isSelect(parent)) {
      return fromSelf(toSelect(parent));
    }

    return parent->toString() == "self";
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
    string genRefName = getInstanceName(inst);
    return genRefName == "dashr";
  }

  static inline bool isShiftOp(Instance& inst) {
    string genRefName = getInstanceName(inst);
    vector<string> bitwiseOps{"dshl", "dlshr", "dashr"};
    return elem(genRefName, bitwiseOps);
  }

  static inline bool isSDivOrRem(Instance& inst) {
    string genRefName = getInstanceName(inst);
    vector<string> bitwiseOps{"sdiv", "srem"};
    return elem(genRefName, bitwiseOps);
  }
  
  static inline bool isUDivOrRem(Instance& inst) {
    string genRefName = getInstanceName(inst);
    vector<string> bitwiseOps{"udiv", "urem"};
    return elem(genRefName, bitwiseOps);
  }

  static inline bool isBitwiseOp(Instance& inst) {
    string genRefName = getInstanceName(inst);
    vector<string> bitwiseOps{"not", "and", "or", "xor", "bitor", "bitand", "bitxor"};
    return elem(genRefName, bitwiseOps);
  }

  static inline bool isSignInvariantOp(Instance& inst) {
    string genRefName = getInstanceName(inst);
    vector<string> siOps{"add", "sub", "mul", "eq"};
    return elem(genRefName, siOps);
  }

  static inline bool isUnsignedCmp(Instance& inst) {
    string genRefName = getInstanceName(inst);
    vector<string> siOps{"ult", "ugt", "ule", "uge"};
    return elem(genRefName, siOps);
  }

  static inline bool isSignedCmp(Instance& inst) {
    string genRefName = getInstanceName(inst);
    vector<string> siOps{"slt", "sgt", "sle", "sge"};
    return elem(genRefName, siOps);
  }
  
}
