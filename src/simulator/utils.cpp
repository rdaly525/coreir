#include "coreir/simulator/utils.h"

#include "coreir/ir/context.h"

#include <fstream>

using namespace CoreIR;
using namespace std;

namespace CoreIR {

  //TODO change the following to use proper coreIR casting
  //isa<>, cast<>, dyn_cast<>
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
        //cout << select.first << "->" + select.second->toString() << endl;
	      outs.insert(select);
      }
    }

    return outs;
  }

  bool recordTypeHasField(const std::string& fieldName, Type* t) {
    //cout << "Target type = " << t->toString() << endl;
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
    for (uint i = 0; i < declStrs.size(); i++) {
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
    string genRefName = inst.getModuleRef()->getName();
    return genRefName;
    
  }

  CoreIR::Wireable*
  findSelect(const std::string& selName,
	     const std::unordered_map<std::string, CoreIR::Wireable*> selects) {
    for (auto& sel : selects) {
      if (sel.first == selName) {
	return sel.second;
      }
    }

    cout << "Could not find select with name = " << selName << endl;
    assert(false);
  }

  bool fromSelfInterface(Select* w) {
    if (!fromSelf(w)) {
      return false;
    }

    Wireable* parent = w->getParent();
    if (isInterface(parent)) {
      return true;
    } else if (isInstance(parent)) {
      return false;
    }

    assert(isSelect(parent));

    return fromSelf(toSelect(parent));
  }

  std::unordered_map<string, Type*>
  outputs(Module& mod) {
    Type* tp = mod.getType();

    assert(tp->getKind() == Type::TK_Record);

    unordered_map<string, Type*> outs;

    RecordType* modRec = static_cast<RecordType*>(tp);
    vector<string> declStrs;
    for (auto& name_type_pair : modRec->getRecord()) {
      Type* tp = name_type_pair.second;

      if (tp->isOutput()) {
        outs.insert(name_type_pair);
      }
    }

    return outs;
    
  }

  std::string getQualifiedOpName(CoreIR::Instance& inst) {
    //cout << "Getting qualified opName of " << inst.toString() << endl;
    auto modRef = inst.getModuleRef();

    ASSERT(modRef != nullptr, "Module ref is NULL");
    std::string opName = modRef->getNamespace()->getName() + "." +
      getOpName(inst);

    return opName;
  }
  
  bool isConstant(CoreIR::Wireable* const w) {
    if (isInstance(w)) {
      string name = getQualifiedOpName(*toInstance(w));

      return (name == "coreir.const") ||
        (name == "corebit.const");
    }

    return false;
  }

  std::vector<char> hexToBytes(const std::string& hex) {
    std::vector<char> bytes;

    for (unsigned int i = 0; i < hex.length(); i += 2) {
      std::string byteString = hex.substr(i, 2);
      char byte = (char) strtol(byteString.c_str(), NULL, 16);
      bytes.push_back(byte);
    }

    return bytes;
  }

  std::vector<std::string> splitStr(const std::string& str,
                                    const std::string& delimiter) {
    std::vector<std::string> strings;

    std::string::size_type pos = 0;
    std::string::size_type prev = 0;
    while ((pos = str.find(delimiter, prev)) != std::string::npos)
      {
        strings.push_back(str.substr(prev, pos - prev));
        prev = pos + 1;
      }

    // To get the last substring (or only, if delimiter is not found)
    strings.push_back(str.substr(prev));

    return strings;
  }

  BitVector hexStringToBitVector(const std::string& str) {
    vector<char> addrBytes = hexToBytes(str);

    //assert(addrBytes.size() == 4);
    int numBits = str.size() * 4;

    reverse(addrBytes);

    BitVector configAddr(numBits, 0);

    int offset = 0;
    for (auto byte : addrBytes) {
      BitVector tmp(8, byte);
      for (uint i = 0; i < (uint) tmp.bitLength(); i++) {
        configAddr.set(offset, tmp.get(i));
        offset++;
      }
    }

    assert(offset == 32);

    return configAddr;
  }

  BitStreamConfig loadConfig(const std::string& configFileName) {
    cout << "Loading configuration state" << endl;

    //configFile("./bitstream/shell_bitstream.bs")
    std::ifstream configFile(configFileName);
    std::string str((std::istreambuf_iterator<char>(configFile)),
                    std::istreambuf_iterator<char>());

    cout << "Config file text" << endl;
    cout << str << endl;

    auto configLines = splitStr(str, "\n");
    cout << "Config lines" << endl;
    for (auto line : configLines) {
      cout << "\t" << line << endl;
    }

    vector<BitVector> configDatas;
    vector<BitVector> configAddrs;

    for (auto line : configLines) {
      auto entries = splitStr(line, " ");

      cout << "# of entries == " << entries.size() << endl;
      cout << "Line = " << line << endl;

      assert(entries.size() == 2);

      string addrString = entries[0];
      string dataString = entries[1];

      cout << "addr string = " << addrString << endl;
      cout << "data string = " << dataString << endl;

      assert(addrString.size() == 8);
      assert(dataString.size() == 8);

      // Convert strings to bit vectors
      vector<char> addrBytes = hexToBytes(addrString);
      assert(addrBytes.size() == 4);

      BitVector configAddr = hexStringToBitVector(addrString);
      BitVector configData = hexStringToBitVector(dataString);

      cout << "configAddr = " << configAddr << endl;
      cout << "configData = " << configData << endl;

      configAddrs.push_back(configAddr);
      configDatas.push_back(configData);
    }

    assert(configAddrs.size() == configLines.size());
    assert(configDatas.size() == configLines.size());

    return {configAddrs, configDatas};
  }

  Module* loadModule(CoreIR::Context* const c,
                     const std::string& fileName,
                     const std::string& topModName) {
    Module* topMod = nullptr;

    if (!loadFromFile(c, fileName, &topMod)) {
      cout << "Could not Load from json!!" << endl;
      c->die();
    }

    topMod = c->getGlobal()->getModule(topModName);

    assert(topMod != nullptr);

    return topMod;
  }

  
}
