#include "coreir/simulator/print_c.h"

using namespace std;

namespace CoreIR {

  std::string cVar(CoreIR::Wireable& w) {
    if (isSelect(w)) {
      CoreIR::Select& s = toSelect(w);
      if (CoreIR::isNumber(s.getSelStr())) {
    	return cVar(*(s.getParent())) + "[" + s.getSelStr() + "]";
      } else {
    	return cVar(*(s.getParent())) + "_" + s.getSelStr();
      }
    } else {

      return w.toString();
    }
  }

  std::string cVar(const std::string& prefix,
		   CoreIR::Wireable& w,
		   const std::string& suffix) {

    if (isSelect(w)) {
      CoreIR::Select& s = toSelect(w);
      if (CoreIR::isNumber(s.getSelStr())) {

	return cVar(prefix, *(s.getParent()), suffix) + "[" + s.getSelStr() + "]";

      } else {

	return prefix + cVar(*(s.getParent())) + "_" + s.getSelStr() + suffix;
      }
    } else {

      return prefix + w.toString() + suffix;
    }
  }
  
  std::string cVar(CoreIR::Wireable& w, const std::string& suffix) {
    return cVar("", w, suffix);
  }

  std::string cVar(const InstanceValue& w) {
    string cv = cVar(*(w.getWire()));

    return cv;
  }

  std::string cVar(const std::string& prefix,
		   const InstanceValue& w,
		   const std::string& suffix) {
    string cv = cVar(prefix, *(w.getWire()), suffix);

    return cv;
  }
  
  std::string cVar(const InstanceValue& w, const std::string& suffix) {
    string cv = cVar(*(w.getWire()), suffix);

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
    } else if (genRefName == "neq") {
      return " != ";
    } else if ((genRefName == "sge") || (genRefName == "uge")) {
      return " >= ";
    } else if ((genRefName == "sle") || (genRefName == "ule")) {
      return " <= ";
    } else if ((genRefName == "sgt") || (genRefName == "ugt")) {
      return " > ";
    } else if ((genRefName == "slt") || (genRefName == "ult")) {
      return " < ";
    } else if (genRefName == "shl") {
      return " << ";
    } else if ((genRefName == "ashr") || (genRefName == "lshr")) {
      return " >> ";
    } else if ((genRefName == "udiv") || (genRefName == "sdiv")) {
      return " / ";
    } else if ((genRefName == "urem") || (genRefName == "srem")) {
      return " % ";
    } else if ((genRefName == "orr")) {
      return "!!";
    } else if (genRefName == "andr") {
      return "andr";
    }

    cout << "ERROR: Unsupported op name = " << genRefName << endl;

    assert(false);
    return "";
  }

  std::string unSignedCTypeString(Type& tp) {
    assert(isPrimitiveType(tp));

    uint w = containerTypeWidth(tp);

    if (w == 8) {
      return "uint8_t";
    }

    if (w == 16) {
      return "uint16_t";
    }

    if (w == 32) {
      return "uint32_t";
    }

    if (w == 64) {
      return "uint64_t";
    }
    
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
    return parens(bitMaskString(endWidth - startWidth) + " << " + to_string(startWidth));
  }

  string lastMask(const std::string& startWidth, const std::string& endWidth) {
    return parens(bitMaskString(parens(endWidth + " - " + startWidth)) + " << " + startWidth);
  }
  

  std::string cPrimitiveTypeString(Type& t) {
    assert(isPrimitiveType(t));

    if (isClkIn(t) || isNamedType(t, "clk")) {
      return "uint8_t" ;
    }

    if (t.getKind() == Type::TK_BitIn) {
      return "uint8_t" ;
    }

    if (t.getKind() == Type::TK_Bit) {
      return "uint8_t" ;
    }

    if (isBitArrayOfLengthLEQ(t, 8)) {
      return "uint8_t" ;
    }

    if (isBitArrayOfLengthLEQ(t, 16)) {
      return "uint16_t" ;
    }
    
    if (isBitArrayOfLengthLEQ(t, 32)) {
      return "uint32_t" ;
    }

    if (isBitArrayOfLengthLEQ(t, 64)) {
      return "uint64_t" ;
    }

    assert(false);

  }

  std::string cArrayTypeDecl(Type& t, const std::string& varName) {

    if (isClkIn(t) || isNamedType(t, "clk")) {
      return "uint8_t " + varName;
    }

    if (t.getKind() == Type::TK_BitIn) {
      return "uint8_t " + varName;
    }

    if (t.getKind() == Type::TK_Bit) {
      return "uint8_t " + varName;
    }

    if (isBitArrayOfLengthLEQ(t, 8)) {
      return "uint8_t " + varName;
    }

    if (isBitArrayOfLengthLEQ(t, 16)) {
      return "uint16_t " + varName;
    }
    
    if (isBitArrayOfLengthLEQ(t, 32)) {
      return "uint32_t " + varName;
    }

    if (isBitArrayOfLengthLEQ(t, 64)) {
      return "uint64_t " + varName;
    }

    if (isBitArray(t)) {
      ArrayType& arrTp = toArray(t);
      int arrLen = arrTp.getLen();
      //int bitLength = (arrLen / 8) + 1 - (arrLen % 8 == 0);

      //return "uint8_t " + varName + "[ " + to_string(bitLength) + " ]";
      return "bit_vector< " + to_string(arrLen) + " > " + varName;
    }
    
    if (isArray(t)) {
      ArrayType& tArr = static_cast<ArrayType&>(t);
      Type& underlying = *(tArr.getElemType());

      return cArrayTypeDecl(underlying, varName + "[ " + std::to_string(tArr.getLen()) + " ]");
    }

    cout << "ERROR: Unsupported type = " << t.toString() << endl;    

    assert(false);

  }

  string maskMacroDef() {
    string expr = "(expr)";
    string width = "(width)";

    return "#define MASK(width, expr) " + parens( bitMaskString(width) +  " & " + parens(expr)) + "\n\n";
  }

  string seMacroDef() {
    string arg = "(x)";
    string startWidth = "(start)";
    string extWidth = "(end)";

    string def = "#define SIGN_EXTEND(start, end, x) ";
    string mask = parens(arg + " & " + bitMaskString(startWidth));

    string testClause = parens(arg + " & " + parens("1ULL << " +
                                                    parens(startWidth + " - 1")));

    string res = parens(mask + " | " +
                        ite(testClause, lastMask(startWidth, extWidth), "0"));
    
    def += res + "\n\n";

    return def;

  }

  
}
