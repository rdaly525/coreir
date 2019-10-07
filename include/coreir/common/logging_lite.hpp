// Copyright: Raj Setaluri 2017
// Author: Raj Setaluri (raj.setaluri@gmail.com)

// This file include a lightweight implementation of the glog LOG macro.

#ifndef COREIR_COMMON_LOGGING_LITE_HPP_
#define COREIR_COMMON_LOGGING_LITE_HPP_

#include <iostream>

enum LogSeverity {
  INFO = 0,
  WARN = 1,
  FATAL
};

namespace common {
namespace internal {

// LoggerWrapper is a thread safe class.
class LoggerWrapper {
 public:
  LoggerWrapper() = default;
  explicit LoggerWrapper(bool abort) : abort_(abort) {}
  bool abort() const { return abort_; }
 private:
  bool abort_ = false;
};

class Logger {
 public:
  Logger(bool alive, bool abort) : alive_(alive), abort_(abort) {}
  Logger(Logger&& that) : alive_(true), abort_(that.abort_) {
    that.alive_ = false;
  }
  Logger(const Logger& that) = delete;
  ~Logger() {
    if (alive_) {
      EndLine();
      if (abort_) {
        Write("Check failed! aborting.");
        EndLine();
        abort();
      }
    }
  }

  template<typename T>
  static void Write(const T& x) { std::cerr << x; }
  static void EndLine() { std::cerr << std::endl; }

 private:
  bool alive_;
  bool abort_;
};

template<typename T> Logger operator<<(Logger&& l, const T& x) {
  Logger::Write(x);
  return std::move(l);
}

template<typename T> Logger operator<<(LoggerWrapper l, const T& x) {
  return std::move(Logger(true, l.abort()) << x);
}

class LoggerVoidify {
 public:
  LoggerVoidify() {}
  template<class T> void operator&(T& x) {}
  template<class T> void operator&(T&& x) {}
};

}  // namespace internal
}  // namespace common

#define LOG(severity)                                                   \
  ::common::internal::LoggerWrapper(severity == FATAL)                  \
      << __FILE__ << ":" << __LINE__ << " "

#define LOG_IF(severity, condition)                                     \
  (!condition) ? ((void) 0) :                                           \
      ::common::internal::LoggerVoidify() & LOG(severity)

#define CHECK(condition) LOG_IF(FATAL, !(condition))

#ifndef NDEBUG
#define DCHECK(condition) CHECK(condition)
#else  // !NDEBUG
#define DCHECK(condition) while(false) CHECK(condition)
#endif  // NDEBUG

#endif  // COREIR_COMMON_LOGGING_LITE_HPP_
