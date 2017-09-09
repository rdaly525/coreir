#pragma once

#include "wire_node.hpp"
#include "utils.hpp"

namespace CoreIR {

  static inline string parens(const std::string& expr) {
    return "(" + expr + ")";
  }

  static inline string bitMaskString(uint w) {
    assert(w > 0);
    return parens(parens("1ULL << " + to_string(w)) + " - 1");
  }

  static inline string bitMaskString(const std::string& w) {
    return parens(parens("1ULL << " + w) + " - 1");
  }
  
  static inline string bitMaskString(CoreIR::Type& tp) {
    uint w = typeWidth(tp);
    return bitMaskString(w);
  }

  static inline string maskResult(CoreIR::Type& tp, const std::string& expr) {
    if (standardWidth(tp)) {
      return expr;
    }

    return parens( bitMaskString(tp) +  " & " + parens(expr));
  }
  

  std::string cVar(const WireNode& w);

  std::string cVar(const WireNode& w, const std::string& suffix);

  static inline std::string ite(const std::string& condition,
		  const std::string& trueRes,
		  const std::string& falseRes) {
    return parens(condition + " ? " + trueRes + " : " + falseRes);
  }


  std::string getOpString(Instance& inst);

  std::string signedCTypeString(Type& tp);

  std::string lastMask(const uint startWidth, const uint endWidth);

  std::string cArrayTypeDecl(CoreIR::Type& t, const std::string& varName);

  std::string cPrimitiveTypeString(CoreIR::Type& t);

}
