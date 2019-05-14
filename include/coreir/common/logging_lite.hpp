// Copyright: Raj Setaluri 2017
// Author: Raj Setaluri (raj.setaluri@gmail.com)

// This file include a lightweight implementation of the glog LOG macro.

#ifndef COREIR_COMMON_LOGGING_LITE_HPP_
#define COREIR_COMMON_LOGGING_LITE_HPP_

#include <iostream>

enum LogSeverity {
  INFO = 0,
  DEBUG,
  FATAL
};

namespace common {
namespace internal {

class LogSeverityStore {
 public:
  static LogSeverity severity() { return severity_; }
  static void set_severity(LogSeverity severity) { severity_ = severity; }

 private:
  static LogSeverity severity_;
};

LogSeverity LogSeverityStore::severity_ = INFO;

// LoggerWrapper is a thread safe class.
class LoggerWrapper {
 public:
  LoggerWrapper(LogSeverity severity) {
    abort_ = (severity == FATAL);
    write_ = (severity == FATAL) or (severity == LogSeverityStore::severity());
  }

  bool abort() const { return abort_; }
  bool write() const { return write_; }

 private:
  bool abort_ = false;
  bool write_ = false;
};

class Logger {
 public:
  Logger(bool alive, bool abort, bool write)
      : alive_(alive),
        abort_(abort),
        write_(write) {}
  Logger(Logger&& that)
      : alive_(true),
        abort_(that.abort_),
        write_(that.write_) {
    that.alive_ = false;
  }
  Logger(const Logger& that) = delete;
  ~Logger() {
    if (alive_) {
      if (write_) EndLine();
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

  bool write() const { return write_; }

 private:
  bool alive_;
  bool abort_;
  bool write_;
};

template<typename T> Logger operator<<(Logger&& l, const T& x) {
  if (l.write()) Logger::Write(x);
  return std::move(l);
}

template<typename T> Logger operator<<(LoggerWrapper l, const T& x) {
  return std::move(Logger(true, l.abort(), l.write()) << x);
}

class LoggerVoidify {
 public:
  LoggerVoidify() {}
  template<class T> void operator&(T& x) {}
  template<class T> void operator&(T&& x) {}
};

}  // namespace internal
}  // namespace common


void SetLogLevelInfo() {
  ::common::internal::LogSeverityStore::set_severity(INFO);
}

void SetLogLevelDebug() {
  ::common::internal::LogSeverityStore::set_severity(DEBUG);
}

#define LOG(severity)                                                   \
  ::common::internal::LoggerWrapper(severity)                           \
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
