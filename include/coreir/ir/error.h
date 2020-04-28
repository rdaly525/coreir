#ifndef COREIR_ERROR_HPP_
#define COREIR_ERROR_HPP_

#include <sstream>
#include <string>

namespace CoreIR {

struct Error {

  bool isfatal = false;
  std::string msg;
  Error() {}
  void fatal() { isfatal = true; }
  void message(std::string s) { msg = msg + s + "\n"; }
};

}  // namespace CoreIR

#endif  // ERROR_HPP_
