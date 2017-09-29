
//For templates. To be included once

namespace CoreIR {

template<class valTy>
struct Underlying2ValueType;

#define U2V_SPECIALIZE(utype,vtype) \
template<> \
struct Underlying2ValueType<utype> { \
  typedef vtype type; \
};

U2V_SPECIALIZE(bool,ConstBool);
U2V_SPECIALIZE(int,ConstInt);
U2V_SPECIALIZE(BitVector,ConstBitVector);
U2V_SPECIALIZE(std::string,ConstString);
U2V_SPECIALIZE(CoreIR::Type*,ConstCoreIRType);

#undef U2V_SPECIALIZE

//Create a map from underlying types (bool,int,etc) to Value::ValueKind
template<class valTy>
struct Underlying2Kind;

#define U2K_SPECIALIZE(utype,vkind) \
template<> \
struct Underlying2Kind<utype> { \
  static const Value::ValueKind kind = Value::vkind; \
};

U2K_SPECIALIZE(bool,VK_ConstBool)
U2K_SPECIALIZE(int,VK_ConstInt)
U2K_SPECIALIZE(BitVector,VK_ConstBitVector)
U2K_SPECIALIZE(std::string,VK_ConstString)
U2K_SPECIALIZE(Type*,VK_ConstCoreIRType)

#undef U2K_SPECIALIZE

//template<>
//ConstPtr Const_impl<bool>(Context* c,bool val);
//
//template<>
//ConstPtr Const_impl<int>(Context* c,int val);
//
//template<>
//ConstPtr Const_impl<BitVector>(Context* c,BitVector val);
//
//template<>
//ConstPtr Const_impl<std::string>(Context* c,std::string val);
//
//template<>
//ConstPtr Const_impl<Type*>(Context* c,Type* val);

}

#endif
