#include <exception>
#include "coreir/common/logging_lite.hpp"
#include "coreir.h"

using namespace CoreIR;

void TestLogInfo() {
  LOG(INFO) << "Hello!";
}

int main() {
  TestLogInfo();
}
