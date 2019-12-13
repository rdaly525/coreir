#ifndef COREIR_PRIMITIVE_HPP_
#define COREIR_PRIMITIVE_HPP_
#include "verilogAST.hpp"
namespace vAST = verilogAST;
namespace CoreIR {
class Primitive {
    std::function<std::unique_ptr<vAST::Expression>()> primitiveExpressionLambda = nullptr;
    public:

    void setPrimitiveExpressionLambda(std::function<std::unique_ptr<vAST::Expression>()> lambda) {
        this->primitiveExpressionLambda = lambda;
    };

    bool hasPrimitiveExpressionLambda() {
        return this->primitiveExpressionLambda != nullptr;
    }

    std::function<std::unique_ptr<vAST::Expression>()> getPrimitiveExpressionLambda() {
        return this->primitiveExpressionLambda;
    }
};
}
#endif 
