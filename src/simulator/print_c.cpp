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

  std::string getOpString(Instance& inst) {
    string genRefName = getInstanceName(inst);

    if (genRefName == "add") {
      return " + ";
    } else if (genRefName == "sub") {
      return " - ";
    } else if (genRefName == "mul") {
      return " * ";
    } else if ((genRefName == "and") || (genRefName == "bitand")) {
      return " & ";
    } else if (genRefName == "or") {
      return " | ";
    } else if ((genRefName == "xor") || (genRefName == "bitxor")) {
      return " ^ ";
    } else if (genRefName == "not") {
      return "~";
    } else if (genRefName == "eq") {
      return " == ";
    } else if ((genRefName == "sge") || (genRefName == "uge")) {
      return " >= ";
    } else if ((genRefName == "sle") || (genRefName == "ule")) {
      return " <= ";
    } else if ((genRefName == "sgt") || (genRefName == "ugt")) {
      return " > ";
    } else if ((genRefName == "slt") || (genRefName == "ult")) {
      return " < ";
    } else if (genRefName == "dshl") {
      return " << ";
    } else if ((genRefName == "dashr") || (genRefName == "dlshr")) {
      return " >> ";
    }

    cout << "ERROR: Unsupported op name = " << genRefName << endl;

    assert(false);

  }

  string signedCTypeString(Type& tp) {
    assert(isPrimitiveType(tp));

    uint w = containerTypeWidth(tp);

    if (w == 8) {
      return "int8_t";
    }

    if (w == 16) {
      return "int16_t";
    }

    if (w == 32) {
      return "int32_t";
    }

    if (w == 64) {
      return "int64_t";
    }
    
    assert(false);
  }

  string lastMask(const uint startWidth, const uint endWidth) {
    return parens(bitMaskString(startWidth) + " << " + to_string(endWidth - startWidth));
  }

  
}
