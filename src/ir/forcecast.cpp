#include "coreir/ir/value.h"
#include "coreir/ir/valuetype.h"
#include "coreir/ir/json.h"
#include "coreir/ir/common.h"

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
  Context* c = vt->getContext();
  switch(vt->getKind()) {
    case ValueType::VTK_Bool: {
      return Const::make(c,(bool) value);
    }
    case ValueType::VTK_Int: {
      ASSERT(0,"Bad cast");
      return nullptr;
    }
    case ValueType::VTK_BitVector: {
      return ConstInt::make(c,cast<BitVectorType>(vt)->getWidth(),value);
    }
    case ValueType::VTK_String: {
      ASSERT(0,"Cannot cast int to string");
      return nullptr;
    }
    case ValueType::VTK_CoreIRType: {
      ASSERT(0,"Cannot cast int to CoreIRType");
      return nullptr;
    }
    case ValueType::VTK_Module: {
      ASSERT(0,"Cannot cast int to Module");
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
Value* TemplatedConst<BitVector>::forceCast(ValueType* vt) const {
  Context* c = vt->getContext();
  switch(vt->getKind()) {
    case ValueType::VTK_Bool: {
      return Const::make(c,(bool) value.as_native_int32());
    }
    case ValueType::VTK_Int: {
      return Const::make(c,value.as_native_int32());
    }
    case ValueType::VTK_BitVector: {
      ASSERT(0,"Bad cast");
      return nullptr;
    }
    case ValueType::VTK_String: {
      ASSERT(0,"Cannot cast BV to string");
      return nullptr;
    }
    case ValueType::VTK_CoreIRType: {
      ASSERT(0,"Cannot cast BV to CoreIRType");
      return nullptr;
    }
    case ValueType::VTK_Module: {
      ASSERT(0,"Cannot cast BV to Module");
      return nullptr;
    }
    case ValueType::VTK_Json: {
      ASSERT(0,"NYI, cast BV to Json");
      return nullptr;
    }
    default: {
      ASSERT(0,"Bad cast");
      return nullptr;
    }
  }
}

template<>
Value* TemplatedConst<std::string>::forceCast(ValueType* vt) const {
  ASSERT(0,"NYI, Casting strings");
  return nullptr;
}

template<>
Value* TemplatedConst<Type*>::forceCast(ValueType* vt) const {
  ASSERT(0,"Cannot cast a Type*");
  return nullptr;
}

template<>
Value* TemplatedConst<Module*>::forceCast(ValueType* vt) const {
  ASSERT(0,"Cannot cast a Module");
  return nullptr;
}

template<>
Value* TemplatedConst<Json>::forceCast(ValueType* vt) const {
  Context* c = vt->getContext();
  switch(vt->getKind()) {
    case ValueType::VTK_Bool: {
      ASSERT(value.type() == Json::value_t::boolean,"Json is not a bool!");
      return Const::make(c,value.get<bool>());
    }
    case ValueType::VTK_Int: {
      ASSERT(value.type() == Json::value_t::number_integer || value.type() == Json::value_t::number_unsigned,"Json not an int");
      return Const::make(c,value.get<int>());
    }
    case ValueType::VTK_BitVector: {
      ASSERT(0,"Cannot cast Json to BV");
      return nullptr;
    }
    case ValueType::VTK_String: {
      return Const::make(c,CoreIR::toString(value));
    }
    case ValueType::VTK_CoreIRType: {
      ASSERT(0,"Cannot cast Json to CoreIRType");
      return nullptr;
    }
    case ValueType::VTK_Module: {
      ASSERT(0,"Cannot cast Json to Module");
      return nullptr;
    }
    case ValueType::VTK_Json: {
      ASSERT(0,"Bad cast");
      return nullptr;
    }
    default: {
      ASSERT(0,"Bad cast");
      return nullptr;
    }
  }
}

template<>
bool TemplatedConst<bool>::canCast(ValueType* vt) const {
  return isa<BoolType>(vt)
      || isa<IntType>(vt)
      || isa<BitVectorType>(vt)
      || isa<JsonType>(vt);

}
template<>
bool TemplatedConst<int>::canCast(ValueType* vt) const {
  return isa<BoolType>(vt)
      || isa<IntType>(vt)
      || isa<BitVectorType>(vt)
      || isa<JsonType>(vt);

}
template<>
bool TemplatedConst<BitVector>::canCast(ValueType* vt) const {
  return isa<BoolType>(vt)
      || isa<IntType>(vt);

}

template<>
bool TemplatedConst<std::string>::canCast(ValueType* vt) const {
  return false;
}

template<>
bool TemplatedConst<CoreIR::Type*>::canCast(ValueType* vt) const {
  return false;
}

template<>
bool TemplatedConst<Module*>::canCast(ValueType* vt) const {
  return false;
}

template<>
bool TemplatedConst<Json>::canCast(ValueType* vt) const {
  return isa<BoolType>(vt)
      || isa<IntType>(vt)
      || isa<StringType>(vt)
      || isa<JsonType>(vt);

}

}

