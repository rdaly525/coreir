#ifndef COREIR_VALUE_HPP_
#define COREIR_VALUE_HPP_

#include "fwd_declare.h"
#include "casting/casting.h"
#include "dynamic_bit_vector.h"

//TODO this is a hack. MOve template definitions to cpp
#include "valuetype.h"

namespace CoreIR {

template<class valTy>
struct Underlying2ValueType;

#define U2V_SPECIALIZE(utype,vtype) \
template<> \
struct Underlying2ValueType<utype> { \
  typedef vtype type; \
};

U2V_SPECIALIZE(bool,BoolType);
U2V_SPECIALIZE(int,IntType);
U2V_SPECIALIZE(BitVector,BitVectorType);
U2V_SPECIALIZE(std::string,StringType);
U2V_SPECIALIZE(CoreIR::Type*,CoreIRType);
U2V_SPECIALIZE(CoreIR::Module*,ModuleType);
U2V_SPECIALIZE(Json,JsonType);

#undef U2V_SPECIALIZE

class Value {
  public:
    enum ValueKind {
      VK_ConstBool=0,
      VK_ConstInt=1,
      VK_ConstBitVector=2,
      VK_ConstString=3,
      VK_ConstCoreIRType=4,
      VK_ConstModule=5,
      VK_ConstJson=6,
      VK_ConstEnd=7,
      VK_Arg=8,
    };
  private :
    ValueKind kind;
  protected :
    ValueType* vtype;
  public :
    Value(ValueType* vtype, ValueKind kind) : kind(kind), vtype(vtype) {}
    virtual ~Value() {}
    ValueKind getKind() const {return kind;}
    ValueType* getValueType() const {return vtype;}
    virtual std::string toString() const = 0;
  public :
    template<typename T>
    const T& get() const {
      if (auto val = dyn_cast<TemplatedConst<T>>(this)) {
        return val->get();
      }
      ValueType* vt = Underlying2ValueType<T>::type::make(vtype->getContext());
      Value* casted = this->forceCast(vt);
      ASSERT(vt == casted->getValueType(),"Bad ForceCast");
      return casted->get<T>();
    }

    virtual bool operator==(const Value& r) const = 0;
    virtual bool operator<(const Value& r) const = 0;
    bool operator!=(const Value& r) const {return !Value::operator==(r);}
    //TODO do the other ones
    friend bool operator==(const Values& l, const Values& r);

    virtual Value* forceCast(ValueType*) const = 0;
    virtual bool canCast(ValueType*) const = 0;
};

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
U2K_SPECIALIZE(Module*,VK_ConstModule)
U2K_SPECIALIZE(Json,VK_ConstJson)

#undef U2K_SPECIALIZE
}

namespace CoreIR {

class Arg : public Value {
  const std::string field;

  public:
    Arg(ValueType* vtype,std::string field) : Value(vtype,VK_Arg), field(field) {}
    static bool classof(const Value* v) {return v->getKind()==VK_Arg;}
    const std::string& getField() const { return field;}
    bool operator==(const Value& r) const override;
    bool operator<(const Value& r) const override;
    std::string toString() const override { return "Arg(" + field + ")";}
    
    Value* forceCast(ValueType*) const override { ASSERT(0,"Cannot get values from an Arg"); }
    virtual bool canCast(ValueType*) const override { return false;}
};

template<typename T> 
Const* Const_impl(Context* c,T val);

#define TSTAMP(utype) \
template<> \
Const* Const_impl<utype>(Context* c,utype val);

TSTAMP(bool)
TSTAMP(int)
TSTAMP(BitVector)
TSTAMP(std::string)
TSTAMP(Type*)
TSTAMP(Module*)
TSTAMP(Json)

#undef TSTAMP


class Const : public Value {
  protected :
    Const(ValueType* vtype, ValueKind kind) : Value(vtype,kind) {}
  public : 
    virtual bool operator==(const Value& r) const override = 0;
    virtual bool operator<(const Value& r) const override = 0;



    static bool classof(const Value* v) {
      return v->getKind() < VK_ConstEnd;
    }
    
    template<typename T>
    static inline typename std::enable_if<std::is_same<T,bool>::value,Const*>::type
    make(Context* c,T val) {
      return Const_impl<bool>(c,val);
    }

    template<typename T>
    static inline typename std::enable_if<!std::is_same<T,Json>::value && !std::is_same<T,bool>::value && std::is_convertible<T,int>::value,Const*>::type
    make(Context* c,T val) {
      return Const_impl<int>(c,val);
    }

    template<typename T>
    static inline typename std::enable_if<std::is_same<T,BitVector>::value,Const*>::type
    make (Context* c,T val) {
      return Const_impl<BitVector>(c,val);
    }
    
    static inline Const* make(Context* c,int width, uint64_t val) {
      return Const_impl<BitVector>(c,BitVector(width,val));
    }
 
    template<typename T>
    static inline typename std::enable_if<!std::is_same<T,Json>::value && std::is_convertible<T,std::string>::value,Const*>::type
    make (Context* c,T val) {
      return Const_impl<std::string>(c,val);
    }

    template<typename T>
    static inline typename std::enable_if<std::is_convertible<T,Type*>::value,Const*>::type
    make(Context* c,T val) {
      return Const_impl<Type*>(c,val);
    }
    
    template<typename T>
    static inline typename std::enable_if<std::is_convertible<T,Module*>::value,Const*>::type
    make(Context* c,T val) {
      return Const_impl<Module*>(c,val);
    }
    
    template<typename T>
    static inline typename std::enable_if<std::is_same<T,Json>::value,Const*>::type
    make(Context* c,T val) {
      return Const_impl<Json>(c,val);
    }

    virtual std::string toString() const override = 0;
    
    virtual Value* forceCast(ValueType*) const override = 0;
    virtual bool canCast(ValueType*) const override = 0;

};


template<typename T>
class TemplatedConst : public Const {
  const T value;
  public :
    //typedef T type;
    TemplatedConst(ValueType* type, T value) : Const(type,Underlying2Kind<T>::kind), value(value) {} //TODO should I check for the typekind matching?
    bool operator==(const Value& r) const override;
    bool operator<(const Value& r) const override;

    static bool classof(const Value* v) {return v->getKind()==Underlying2Kind<T>::kind;}
    
    std::string toString() const override;
    const T& get() const { return value;}
  
    Value* forceCast(ValueType*) const override;
    bool canCast(ValueType*) const override;

};

}
#endif
