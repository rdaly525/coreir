#pragma once

#include <fstream>
#include <streambuf>
#include <string>
#include "coreir/passes/common.h"

void assertPassEq(CoreIR::Context* c, std::string ID, std::string golden_path) {
  if (ID == "coreirjson") { c->runPasses({"coreirjson"}, {"global"}); }
  auto pass = c->getPassManager()->getAnalysisPass(ID);
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
