#ifndef ERROR_HPP_
#define ERROR_HPP_

struct Error {
  
  bool isfatal;
  string msg;
  Error() {isfatal = false;}
  void fatal() { isfatal = true;}
  void message(string s) { msg = msg + s + "\n"; }
  string toString() { return msg; }
};

#endif //ERROR_HPP_
