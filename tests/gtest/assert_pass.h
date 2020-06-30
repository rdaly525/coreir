#pragma once

#include <fstream>
#include <streambuf>
#include <string>
#include "coreir/passes/common.h"

template <typename T>
void assertPassEq(CoreIR::Context* c, std::string golden_path) {
  auto pass = static_cast<T*>(c->getPassManager()->getAnalysisPass(T::ID));
  std::ostringstream stream;
  pass->writeToStream(stream);
  const std::string result = stream.str();

  std::ifstream golden_stream(golden_path);
  ASSERT_TRUE(golden_stream.good());

  std::string golden(
    (std::istreambuf_iterator<char>(golden_stream)),
    std::istreambuf_iterator<char>());
  EXPECT_EQ(golden, result);
}
