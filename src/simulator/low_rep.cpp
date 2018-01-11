#include "coreir/simulator/low_rep.h"

#include <iostream>

using namespace std;

namespace CoreIR {

  string LowProgram::cString() const {
    string res = "";

    for (auto& stmt : stmts) {
      assert(stmt != nullptr);

      res += stmt->cString();
    }

    return res;
  }

  std::string LowId::cString() const {
    return name;
  }

}
