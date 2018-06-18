#include "coreir/ir/value.h"
#include "coreir/ir/valuetype.h"
#include "coreir/ir/json.h"

namespace CoreIR {


//Cast to bool
template<>
Value* TemplatedConst<bool>::forceCast(ValueType* vt) const {
  Context* c = vt->getContext();
  switch(vt->getKind()) {
    case ValueType::VTK_Bool: {
      ASSERT(0,"Bad cast");
      return nullptr;
    }
    case ValueType::VTK_Int: {
      return Const::make(c,(int) value);
    }
    case ValueType::VTK_BitVector: {
      return ConstInt::make(c,cast<BitVectorType>(vt)->getWidth(),(int) value);
    }
    case ValueType::VTK_String: {
      ASSERT(0,"Cannot cast bool to string");
      return nullptr;
    }
    case ValueType::VTK_CoreIRType: {
      ASSERT(0,"Cannot cast bool to CoreIRType");
      return nullptr;
    }
    case ValueType::VTK_Module: {
      ASSERT(0,"Cannot cast bool to Module");
      return nullptr;
    }
    case ValueType::VTK_Json: {
      Json jval = value;
      return Const::make(c,jval);
    }
    default: {
      ASSERT(0,"Bad cast");
      return nullptr;
    }
  }

}

template<>
Value* TemplatedConst<int>::forceCast(ValueType* vt) const {
  ASSERT(0,"NYI");
  return nullptr;
}

template<>
Value* TemplatedConst<BitVector>::forceCast(ValueType* vt) const {
  ASSERT(0,"NYI");
  return nullptr;
}

template<>
Value* TemplatedConst<std::string>::forceCast(ValueType* vt) const {
  ASSERT(0,"NYI");
  return nullptr;
}

template<>
Value* TemplatedConst<Type*>::forceCast(ValueType* vt) const {
  ASSERT(0,"NYI");
  return nullptr;
}

template<>
Value* TemplatedConst<Module*>::forceCast(ValueType* vt) const {
  ASSERT(0,"NYI");
  return nullptr;
}

template<>
Value* TemplatedConst<Json>::forceCast(ValueType* vt) const {
  ASSERT(0,"NYI");
  return nullptr;
}


}

