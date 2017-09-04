#include "print_c.hpp"

namespace CoreIR {

  std::string cVar(const WireNode& w) {
    string cv = cVar(*(w.getWire()));
    if (w.isSequential) {
      if (w.isReceiver) {
	return cv += "_receiver";
      } else {
	return cv += "_source";
      }

    }
    return cv;
  }

  std::string cVar(const WireNode& w, const std::string& suffix) {
    string cv = cVar(*(w.getWire()), suffix);
    if (w.isSequential) {
      if (w.isReceiver) {
	return cv += "_receiver";
      } else {
	return cv += "_source";
      }

    }
    return cv;
  }

  
}
