#ifndef ERROR_HPP_
#define ERROR_HPP_
#include <sstream>
#include <string>

namespace CoreIR {

struct Error {
  
  bool isfatal;
  string msg;
  Error() {isfatal = false;}
  void fatal() { isfatal = true;}
  void message(string s) { msg = msg + s + "\n"; }
  string toString() { return msg; }
  //friend void operator<<(Error e, std::ostream& s) {
  //  std::ostringstream os;
  //  e.msg += s.str();
  //}
};

}//CoreIR namespace


#endif //ERROR_HPP_
