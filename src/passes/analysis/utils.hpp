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

    assert(genRef != nullptr);

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

  
  std::string cTypeString(CoreIR::Type& t);

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

}
