#include <exception>
#include "coreir.h"
#include "coreir/common/logging_lite.hpp"

using namespace CoreIR;

void TestLogInfo() { LOG(INFO) << "Hello!"; }

void TestLogDebug() {
  DLOG(INFO) << "Debug Hello!";
  ::common::SetLogLevel(DEBUG);
  DLOG(INFO) << "Debug Hello!";
}

int main() {
  TestLogInfo();
  TestLogDebug();
}
