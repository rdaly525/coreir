#pragma once

#include <fstream>
#include <streambuf>
#include <string>
#include "coreir/passes/common.h"

template<typename T>
void assertPassEq(CoreIR::Context* c, std::string golden_path) {
  auto pass = static_cast<T*>(c->getPassManager()->getAnalysisPass(T::ID));
  std::ostringstream stream;
  pass->writeToStream(stream);
  const std::string result = stream.str();

  std::ifstream golden_stream(golden_path);
  ASSERT(golden_stream.good(), "Can't read " + golden_path);

  std::string golden((std::istreambuf_iterator<char>(golden_stream)),
                     std::istreambuf_iterator<char>());
  ASSERT(golden == result,
         golden_path + ": Expected '" + golden + "' but got '" + result + "'");
}
