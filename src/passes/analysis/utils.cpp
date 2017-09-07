#include "utils.hpp"

using namespace CoreIR;

namespace CoreIR {

  bool isBitArray(Type& t) {
    if (t.getKind() != Type::TK_Array) {
      return false;
    }

    ArrayType& tArr = static_cast<ArrayType&>(t);

    Type::TypeKind elemKind = (tArr.getElemType())->getKind();
    if ((elemKind == Type::TK_Bit || elemKind == Type::TK_BitIn)) {
      return true;
    }

    return false;
  }

  bool isBitArrayOfLength(Type& t, const uint len) {
    if (t.getKind() != Type::TK_Array) {
      return false;
    }

    ArrayType& tArr = static_cast<ArrayType&>(t);

    Type::TypeKind elemKind = (tArr.getElemType())->getKind();
    if ((elemKind == Type::TK_Bit || elemKind == Type::TK_BitIn) &&
	(tArr.getLen() == len)) {
      return true;
    }

    return false;
  }

  bool isBitArrayOfLengthLEQ(Type& t, const uint len) {
    if (t.getKind() != Type::TK_Array) {
      return false;
    }

    ArrayType& tArr = static_cast<ArrayType&>(t);

    Type::TypeKind elemKind = (tArr.getElemType())->getKind();
    if ((elemKind == Type::TK_Bit || elemKind == Type::TK_BitIn) &&
	(tArr.getLen() <= len)) {
      return true;
    }

    return false;
  }
  
  bool isPrimitiveType(Type& t) {

    if ((t.getKind() == Type::TK_BitIn) ||
	(t.getKind() == Type::TK_Bit)) {
      return true;
    }
    
    if (isBitArrayOfLengthLEQ(t, 8)) {
      return true;
    }

    if (isBitArrayOfLengthLEQ(t, 16)) {
      return true;
    }
    
    if (isBitArrayOfLengthLEQ(t, 32)) {
      return true;
    }

    if (isBitArrayOfLengthLEQ(t, 64)) {
      return true;
    }

    return false;
  }

  unordered_map<string, Wireable*>
  getOutputSelects(Wireable* inst) {
    unordered_map<string, Wireable*> outs;

    for (auto& select : inst->getSelects()) {
      if (select.second->getType()->isOutput()) {
	outs.insert(select);
      }
    }

    return outs;
  }

  unordered_map<string, Wireable*>
  getInputSelects(Wireable* inst) {
    unordered_map<string, Wireable*> outs;

    for (auto& select : inst->getSelects()) {
      if (select.second->getType()->isInput()) {
	outs.insert(select);
      }
    }

    return outs;
  }

  bool recordTypeHasField(const std::string& fieldName, Type* t) {
    cout << "Target type = " << t->toString() << endl;
    assert(t->getKind() == Type::TK_Record);

    RecordType* rt = static_cast<RecordType*>(t);

    for (auto& rec : rt->getRecord()) {
      if (rec.first == fieldName) {
	return true;
      }
    }
    
    return false;
  }


  std::string commaSepList(std::vector<std::string>& declStrs) {
    std::string res = "";
    for (int i = 0; i < declStrs.size(); i++) {
      res += declStrs[i];
      if (i < declStrs.size() - 1) {
	res += ", ";
      }
    }

    return res;
    
  }

  uint typeWidth(CoreIR::Type& tp) {  
    //cout << "typeWidth = " << tp.toString() << endl;

    assert(isPrimitiveType(tp));

    if ((tp.getKind() == Type::TK_BitIn) ||
	(tp.getKind() == Type::TK_Bit)) {
      return 1;
    }

    if (isBitArrayOfLengthLEQ(tp, 64)) {
      CoreIR::ArrayType& arrTp = toArray(tp);
      return arrTp.getLen();
    }

    cout << "ERROR: No type width for " << tp.toString() << endl;
    assert(false);
  }

  uint containerTypeWidth(Type& tp) {
    uint w = typeWidth(tp);

    assert(w <= 64);

    if (w <= 8) {
      return 8;
    }

    if (w <= 16) {
      return 16;
    }

    if (w <= 32) {
      return 32;
    }

    if (w <= 64) {
      return 64;
    }

    assert(false);
  }

  bool standardWidth(Type& tp) {
    uint w = typeWidth(tp);

    if ((w == 8) || (w == 16) || (w == 32) || (w == 64)) {
      return true;
    }

    return false;
  }


  bool connectionIsOrdered(const Connection& connection) {
    Wireable* fst = connection.first;
    Wireable* snd = connection.second;

    assert(isSelect(fst));
    assert(isSelect(snd));

    // Is this the same as fst->getParent()->getType() ?? No, I dont think so
    Type* fst_tp = fst->getType();
    Type* snd_tp = snd->getType();

    if ((fst_tp->isInput() && snd_tp->isOutput()) ||
	(fst_tp->isOutput() && snd_tp->isInput())) {
      return true;
    }

    return false;
  }


  std::string getOpName(Instance& inst) {
    string genRefName = inst.getGeneratorRef()->getName();
    return genRefName;
  }
  
}
