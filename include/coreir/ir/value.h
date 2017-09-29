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

U2V_SPECIALIZE(bool,ConstBool);
U2V_SPECIALIZE(int,ConstInt);
U2V_SPECIALIZE(BitVector,ConstBitVector);
U2V_SPECIALIZE(std::string,ConstString);
U2V_SPECIALIZE(CoreIR::Type*,ConstCoreIRType);

#undef U2V_SPECIALIZE

class Value {
  public:
    enum ValueKind {
      VK_ConstBool=0,
      VK_ConstInt=1,
      VK_ConstBitVector=2,
      VK_ConstString=3,
      VK_ConstCoreIRType=4,
      VK_ConstEnd=5,
      VK_Arg=6,
      VK_CPPLambda=7
    };
  private :
    ValueKind kind;
    ValueType* vtype;
  public :
    Value(ValueType* vtype, ValueKind kind) : kind(kind), vtype(vtype) {}
    ValueKind getKind() const {return kind;}
    ValueType* getValueType() const {return vtype;}
    virtual std::string toString() const = 0;
    virtual bool operator==(const Value& r) const;
  friend bool operator==(const Values& l, const Values& r);
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

#undef U2K_SPECIALIZE
}

namespace CoreIR {
class Arg : public Value {
  std::string field;
  public :
    Arg(ValueType* vtype,std::string field) : Value(vtype,VK_Arg) {}
    static bool classof(const Value* v) {return v->getKind()==VK_Arg;}
    static ArgPtr make(ValueType* vtype, std::string field) {
      return std::make_shared<Arg>(vtype,field);
    }
    std::string getField() { return field;}
    bool operator==(const Value& r) const;
    std::string toString() const { return "Arg(" + field + ")";}
};

//class CPPLambda : public Value {
//  public :
//    typedef std::function<Const(Consts,Consts)> LambdaType;
//    CPPLambda(ValueType* vtype,LambdaType lambda) : Value(VK_CPPLambda), lambda(lambda) {}
//    static bool classof(const Value* v) {return v->getKind()==VK_CPPLambda;}
//    static std::shared_ptr<CPPLambda> make(LambdaType lambda) {
//      return std::make_shared<CPPLambda>(lambda);
//    } 
//  private :
//    LambdaType lambda;
//  public :
//    bool operator==(const Value& r) const {
//      return false;
//    }
//};

template<typename T> 
ConstPtr Const_impl(Context* c,T val);

#define TSTAMP(utype) \
template<> \
ConstPtr Const_impl<utype>(Context* c,utype val);

TSTAMP(bool)
TSTAMP(int)
TSTAMP(BitVector)
TSTAMP(std::string)
TSTAMP(Type*)

#undef TSTAMP


class Const : public Value {
  protected :
    Const(ValueType* vtype, ValueKind kind) : Value(vtype,kind) {}
  public : 
    static bool classof(const Value* v) {
      return v->getKind() < VK_ConstEnd;
    }
    
    template<typename T>
    static inline typename std::enable_if<std::is_same<T,bool>::value,ConstPtr>::type
    make(Context* c,T val) {
      return Const_impl<bool>(c,val);
    }

    template<typename T>
    static inline typename std::enable_if<!std::is_same<T,bool>::value && std::is_convertible<T,int>::value,ConstPtr>::type
    make(Context* c,T val) {
      return Const_impl<int>(c,val);
    }

    template<typename T>
    static inline typename std::enable_if<std::is_same<T,BitVector>::value,ConstPtr>::type
    make (Context* c,T val) {
      return Const_impl<BitVector>(c,val);
    }
    
    template<typename T>
    static inline typename std::enable_if<std::is_convertible<T,std::string>::value,ConstPtr>::type
    make (Context* c,T val) {
      return Const_impl<std::string>(c,val);
    }

    template<typename T>
    static inline typename std::enable_if<std::is_convertible<T,Type*>::value,ConstPtr>::type
    make(Context* c,T val) {
      return Const_impl<Type*>(c,val);
    }

    virtual std::string toString() const override = 0;

    template<typename T>
    T get() {
      return cast<typename Underlying2ValueType<T>::type>(this)->get();
    }

};


//T should be bool,BitVector,int,string,Type
template<typename T>
class TemplatedConst : public Const {
  T value;
  public :
    //typedef T type;
    TemplatedConst(ValueType* type, T value) : Const(type,Underlying2Kind<T>::kind), value(value) {}
    static bool classof(const Value* v) {return v->getKind()==Underlying2Kind<T>::kind;}
    static std::shared_ptr<TemplatedConst<T>> make(ValueType* type, T value) {
      return std::make_shared<TemplatedConst<T>>(type,value);
    }
    
    std::string toString() const override {
      return "NYI";
    }
    T get() { return value;}
};


}

#endif
