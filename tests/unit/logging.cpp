#include <exception>
#include "coreir/common/logging_lite.hpp"
#include "coreir.h"

using namespace CoreIR;

void TestLogInfo() {
  LOG(INFO) << "Hello!";
}

void TestLogDebug() {
  LOG(DEBUG) << "Debug Hello!";
  ::common::SetLogLevel(DEBUG);
  LOG(DEBUG) << "Debug Hello!";
}

int main() {
  TestLogInfo();
  TestLogDebug();
}
