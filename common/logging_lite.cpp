// Copyright: Raj Setaluri 2019
// Author: Raj Setaluri (raj.setlauri@gmail.com)

#include "coreir/common/logging_lite.hpp"

namespace common {
namespace internal {

namespace {
class LogSeverityStore {
 public:
  static LogSeverity severity() { return severity_; }
  static void set_severity(LogSeverity severity) { severity_ = severity; }

 private:
  static LogSeverity severity_;
};

LogSeverity LogSeverityStore::severity_ = INFO;

}  // namespace

Logger::~Logger() {
  if (alive_) {
    if (write_) EndLine();
    if (abort_) {
      Write("Check failed! aborting.");
      EndLine();
      abort();
    }
  }
}

}  // namespace internal

void SetLogLevel(int severity) {
  const auto as_severity = static_cast<LogSeverity>(severity);
  internal::LogSeverityStore::set_severity(as_severity);
}

LogSeverity GetLogLevel() { return internal::LogSeverityStore::severity(); }

}  // namespace common
