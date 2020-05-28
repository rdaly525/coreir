#pragma once

#include "coreir/ir/fwd_declare.h"
#include "verilogAST.hpp"

namespace vAST = verilogAST;
namespace CoreIR {
class VerilogPrimitive {
  std::function<std::unique_ptr<vAST::Expression>()>
    primitiveExpressionLambda = nullptr;

 public:
  void setPrimitiveExpressionLambda(
    std::function<std::unique_ptr<vAST::Expression>()> lambda) {
    this->primitiveExpressionLambda = lambda;
  };

  bool hasPrimitiveExpressionLambda() {
    return this->primitiveExpressionLambda != nullptr;
  }

  std::function<std::unique_ptr<vAST::Expression>()>
  getPrimitiveExpressionLambda() {
    return this->primitiveExpressionLambda;
  }
};
}  // namespace CoreIR
