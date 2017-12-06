#include "coreir/simulator/low_rep.h"

#include <iostream>

using namespace std;

namespace CoreIR {

  string LowProgram::cString() const {
    string res = "";
    cout << "In cString()" << endl;
    for (auto& stmt : stmts) {
      assert(stmt != nullptr);

      cout << "Statement type = " << stmt->getType() << endl;

      cout << "Calling cString on stmt ptr = " << stmt << endl;
      res += stmt->cString();
    }

    cout << "Done with cString()" << endl;
    return res;
  }

  std::string LowId::cString() const {
    cout << "Calling lowid cstring" << endl;
    return name;
  }

}
