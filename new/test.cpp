#include <iostream>
#include <memory>
#include "coreir_context.hpp"

int main(int argc, char** argv) {
  using namespace CoreIR;

  auto context = std::make_unique<CoreIRContext>();
  std::vector<std::shared_ptr<Type>> types;
  types.push_back(std::static_pointer_cast<Type>(context->Bit()));
  types.push_back(std::static_pointer_cast<Type>(context->BitIn()));
  types.push_back(std::static_pointer_cast<Type>(context->BitInOut()));
  for (auto x : types) {
    std::cout << x->toString() << std::endl;
  }
}
