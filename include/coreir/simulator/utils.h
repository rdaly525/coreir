#pragma once

#include "coreir/ir/common.h"
#include "coreir/ir/dynamic_bit_vector.h"
#include "coreir/ir/module.h"
#include "coreir/ir/namespace.h"
#include "coreir/ir/types.h"
#include "coreir/ir/wireable.h"

#include "coreir/simulator/algorithm.h"

namespace CoreIR {

  static inline
  std::string getInstanceName(Instance& w) {
    return w.getModuleRef()->getName();
  }

  static inline int selectNum(CoreIR::Select* const sel) {
    std::string selStr = sel->getSelStr();
    assert(CoreIR::isNumber(selStr));
    int index = std::stoi(selStr);
    return index;
  }

  
  static inline bool arrayAccess(Select* in) {
    return isNumber(in->getSelStr());
  }

  static inline bool isSelect(CoreIR::Wireable* fst) {
    return isa<Select>(fst);
  }

  static inline CoreIR::Select* toSelect(CoreIR::Wireable* w) {
    //cast<> already asserts if wrong type
    return cast<Select>(w);
    //assert(isSelect(w));
  }

  static inline bool isSelect(const CoreIR::Wireable& fst) {
    return isa<Select>(fst);
  }

  static inline CoreIR::Select& toSelect(CoreIR::Wireable& fst) {
    //cast<> already throws assert if wrong type
    return cast<Select>(fst);
    //assert(isSelect(fst));
  }

  static inline bool fromSelf(CoreIR::Select* w) {
    
    //I already have this function
    Wireable* topParent = w->getTopParent();
    return isa<Interface>(topParent);


    //CoreIR::Wireable* parent = w->getParent();
    //if (isSelect(parent)) {
    //  return fromSelf(toSelect(parent));
    //}

    //return parent->toString() == "self";
  }

  
  static inline bool isInstance(CoreIR::Wireable* fst) {
    return isa<Instance>(fst);
  }

  static inline bool isInterface(CoreIR::Wireable* fst) {
    return isa<Interface>(fst);
  }
  
  static inline CoreIR::Instance* toInstance(CoreIR::Wireable* fst) {
    assert(isInstance(fst));
    return cast<Instance>(fst);
  }

  static inline bool isDFFInstance(CoreIR::Wireable* fst) {
    if (!isInstance(fst)) {
      return false;
    }

    CoreIR::Instance* inst = toInstance(fst);
    std::string name = inst->getModuleRef()->getRefName();

    return name == "corebit.reg";
  }

  static inline bool isRegisterInstance(CoreIR::Wireable* fst) {
    //cout << "checking isRegisterInstance " << fst->toString() << endl;
    
    if (auto inst = dyn_cast<Instance>(fst)) {
      Module* m = inst->getModuleRef();
      //module's name is always either the modules name or the generators name
      //m->getLongName() is a uniquified name for generated modules
      //TODO really should be checking m->getRefName() == "coreir.reg"
      return m->getRefName() == "coreir.reg";
    }
    return false;



    //if (!isInstance(fst)) {
    //  return false;
    //}

    ////cout << "Is instance" << endl;

    //CoreIR::Instance* inst = toInstance(fst);

    //auto genRef = inst->getGeneratorRef();

    ////cout << "genRef is null ? " << (genRef == nullptr) << endl;

    //if (genRef == nullptr) {
    //  //std::cout << "ERROR: genRef is null for " << fst->toString() << std::endl;

    //  Module* modRef = inst->getModuleRef();

    //  //std::cout << "Module ref is null ? " << (modRef == nullptr) << std::endl;

    //  assert(modRef != nullptr);

    //  //cout << "Module ref name = " << modRef->getName() << endl;      

    //  return modRef->getName() == "reg";
    //}

    //std::string genRefName = genRef->getName();

    //return genRefName == "reg";
  }

  static inline bool isMemoryInstance(CoreIR::Wireable* fst) {
    
    if (auto inst = dyn_cast<Instance>(fst)) {
      Module* m = inst->getModuleRef();
      return m->getName() == "mem";
    }
    return false;
 



    //if (!isInstance(fst)) {
    //  return false;
    //}

    //CoreIR::Instance* inst = toInstance(fst);

    //auto genRef = inst->getGeneratorRef();

    //if (genRef == nullptr) {
    //  Module* modRef = inst->getModuleRef();

    //  assert(modRef != nullptr);

    //  return modRef->getName() == "mem";
    //}

    //std::string genRefName = genRef->getName();

    //return genRefName == "mem";
  }

  static inline bool isLinebufferMemInstance(CoreIR::Wireable* fst) {
    if (!isInstance(fst)) {
      return false;
    }
    
    return cast<Instance>(fst)->getModuleRef()->getRefName() == "memory.rowbuffer";


    //CoreIR::Instance* inst = toInstance(fst);

    //auto genRef = inst->getGeneratorRef();

    //if (genRef == nullptr) {
    //  Module* modRef = inst->getModuleRef();

    //  assert(modRef != nullptr);

    //  return modRef->getName() == "LinebufferMem";
    //}

    //std::string genRefName = genRef->getName();

    //return genRefName == "LinebufferMem";
  }
  
  static inline bool isNamedType(CoreIR::Type& t, const std::string& name) {
    
    //Can only convert to bool if casting to a pointer
    if (NamedType* namedType = dyn_cast<NamedType>(&t)) {
      return namedType->getName() == name;
    }
    return false;
    
    //if (t.getKind() != CoreIR::Type::TK_Named) {
    //  return false;
    //}

    //CoreIR::NamedType& nt = static_cast<CoreIR::NamedType&>(t);
    //return nt.getName() == name;

  }

  
  static inline bool isArray(CoreIR::Type& t) {
    return isa<ArrayType>(t);

    //return t.getKind() == CoreIR::Type::TK_Array;
  }

  static inline bool isClkIn(CoreIR::Type& t) {
    return isNamedType(t, "clk"); //isNamedType(t, "clkIn");
  }

  
  bool isBitArray(CoreIR::Type& t);
  bool isBitArrayOfLength(CoreIR::Type& t, const uint len);
  bool isBitArrayOfLengthLEQ(CoreIR::Type& t, const uint len);
  bool isPrimitiveType(CoreIR::Type& t);

  std::unordered_map<std::string, CoreIR::Wireable*>
  getOutputSelects(CoreIR::Wireable* inst);

  std::unordered_map<std::string, CoreIR::Wireable*>
  getInputSelects(CoreIR::Wireable* inst);

  bool recordTypeHasField(const std::string& fieldName, CoreIR::Type* t);

  std::string commaSepList(std::vector<std::string>& declStrs);

  static inline std::string selectInfoString(CoreIR::Wireable* w) {
    assert(isSelect(w));

    CoreIR::Select* s = static_cast<CoreIR::Select*>(w);
    std::string ss = s->getSelStr();

    return ss + " " + s->getType()->toString();
  }

  uint typeWidth(CoreIR::Type& tp);

  uint containerTypeWidth(CoreIR::Type& tp);

  bool standardWidth(CoreIR::Type& tp);

  static inline CoreIR::ArrayType& toArray(CoreIR::Type& tp) {
    assert(isArray(tp));

    return static_cast<CoreIR::ArrayType&>(tp);
  }


  bool connectionIsOrdered(const CoreIR::Connection& connection);

  std::string getOpName(CoreIR::Instance& inst);

  std::string getQualifiedOpName(CoreIR::Instance& inst);
  
  static inline Generator* getGeneratorRef(Instance& w) {
    Module* m = w.getModuleRef();
    assert(m->isGenerated());
    return m->getGenerator();

    //auto g = w.getGeneratorRef();

    //assert(g != nullptr);

    //return g;
  }

  static inline bool isDASHR(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    return genRefName == "ashr";
  }

  static inline bool isShiftOp(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> bitwiseOps{"shl", "lshr", "ashr"};
    return elem(genRefName, bitwiseOps);
  }

  static inline bool isSDivOrRem(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> bitwiseOps{"sdiv", "srem"};
    return elem(genRefName, bitwiseOps);
  }
  
  static inline bool isUDivOrRem(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> bitwiseOps{"udiv", "urem"};
    return elem(genRefName, bitwiseOps);
  }

  static inline bool isBitwiseOp(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> bitwiseOps{"not", "and", "or", "xor", "bitor", "bitand", "bitxor"};
    return elem(genRefName, bitwiseOps);
  }

  static inline bool isSignInvariantOp(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> siOps{"add", "sub", "mul", "eq", "neq"};
    return elem(genRefName, siOps);
  }

  static inline bool isAddOrSub(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> siOps{"add", "sub"};
    return elem(genRefName, siOps);
  }
  
  static inline bool isUnsignedCmp(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> siOps{"ult", "ugt", "ule", "uge"};
    return elem(genRefName, siOps);
  }

  static inline bool isSignedCmp(Instance& inst) {
    std::string genRefName = getInstanceName(inst);
    std::vector<std::string> siOps{"slt", "sgt", "sle", "sge"};
    return elem(genRefName, siOps);
  }

  CoreIR::Wireable*
  findSelect(const std::string& selName,
	     const std::unordered_map<std::string, CoreIR::Wireable*> selects);

  static inline int arrayLen(CoreIR::Select* const parent) {
    Type& t = *(parent->getType());
    ArrayType& arrTp = toArray(t);
    int arrLen = arrTp.getLen();
    return arrLen;
  }

  static inline int parentArrayLen(CoreIR::Select* const sel) {
    Select* parent = toSelect(sel->getParent());
    return arrayLen(parent);
  }

  std::unordered_map<std::string, CoreIR::Type*>
  outputs(CoreIR::Module& mod);

  bool fromSelfInterface(CoreIR::Select* w);

  bool isConstant(CoreIR::Wireable* const w);

  struct BitStreamConfig {
    std::vector<BitVector> configAddrs;
    std::vector<BitVector> configDatas;
  };

  BitStreamConfig loadConfig(const std::string& configFileName);

  Module* loadModule(CoreIR::Context* const c,
                     const std::string& fileName,
                     const std::string& topModName);
  
  std::vector<std::string> splitStr(const std::string& str,
                                    const std::string& delimiter);

}
