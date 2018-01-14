#pragma once

#include "coreir/simulator/op_graph.h"
#include "coreir/simulator/utils.h"

namespace CoreIR {

  static inline std::string parens(const std::string& expr) {
    return "(" + expr + ")";
  }

  static inline std::string bitMaskString(uint w) {
    assert(w > 0);
    return parens(parens("1ULL << " + std::to_string(w)) + " - 1");
  }

  static inline std::string bitMaskString(const std::string& w) {
    return parens(parens("1ULL << " + w) + " - 1");
  }
  
  static inline std::string bitMaskString(CoreIR::Type& tp) {
    uint w = typeWidth(tp);
    return bitMaskString(w);
  }

  static inline std::string maskResultStr(const uint w,
					  const std::string& expr) {
    return "MASK( " + std::to_string(w) + ", " + expr + " )";
  }

  static inline std::string maskResult(CoreIR::Type& tp, const std::string& expr) {
    if (standardWidth(tp)) {
      return expr;
    }

    return maskResultStr(typeWidth(tp), expr);
  }
  

  std::string cVar(const InstanceValue& w);

  std::string cVar(const InstanceValue& w, const std::string& suffix);

  std::string cVar(const std::string& prefix,
		   const InstanceValue& w,
		   const std::string& suffix);

  std::string cVar(CoreIR::Wireable& w);

  std::string cVar(const std::string& prefix,
		   CoreIR::Wireable& w,
		   const std::string& suffix);

  std::string cVar(CoreIR::Wireable& w, const std::string& suffix);

  static inline std::string ite(const std::string& condition,
		  const std::string& trueRes,
		  const std::string& falseRes) {
    std::string cntrlMask =
      parens(parens(parens(parens("int") + condition) + " << 31") + " >> 31") +
      " | ";
    return parens(condition + " ? " + trueRes + " : " + falseRes);
    //std::string cnd = "true";
    //return parens(cnd + " ? " + trueRes + " : " + falseRes);
  }


  std::string getOpString(Instance& inst);

  std::string signedCTypeString(Type& tp);
  std::string unSignedCTypeString(Type& tp);

  std::string lastMask(const std::string& startWidth, const std::string& endWidth);

  std::string lastMask(const uint startWidth, const uint endWidth);

  std::string cArrayTypeDecl(CoreIR::Type& t, const std::string& varName);

  std::string cPrimitiveTypeString(CoreIR::Type& t);

  static inline std::string ln(const std::string& s) {
    return s + ";\n";
  }
  
}
