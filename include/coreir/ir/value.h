#ifndef COREIR_VALUE_HPP_
#define COREIR_VALUE_HPP_

#include "fwd_declare.h"

//TODO this is a hack. MOve template definitions to cpp
#include "valuetype.h"

namespace CoreIR {

class Value {
  public:
    enum ValueKind {
      VK_ConstBool=0,
      VK_ConstInt=1,
      VK_ConstString=2,
      VK_ConstType=3,
      VK_ConstEnd=4,
      VK_Arg=5,
      VK_CPPLambda=6
    };
  private :
    ValueKind kind;
    ValueType* vtype;
  public :
    Value(ValueType* vtype, ValueKind kind) : kind(kind), vtype(vtype) {}
    ValueKind getKind() const {return kind;}
    ValueType* getValueType() const {return vtype;}
    virtual std::string toString() const = 0;
};

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
ConstPtr Const_impl(T val);

template<>
ConstPtr Const_impl<bool>(bool val);
template<>
ConstPtr Const_impl<int>(int val);
template<>
ConstPtr Const_impl<std::string>(std::string val);
template<>
ConstPtr Const_impl<Type*>(Type* val);


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
      return Const_impl<bool>(val);
    }

    template<typename T>
    static inline typename std::enable_if<!std::is_same<T,bool>::value && std::is_convertible<T,int>::value,ConstPtr>::type
    make(Context* c,T val) {
      return Const_impl<int>(IntType::make(c,val));
    }
    template<typename T>
    static inline typename std::enable_if<std::is_convertible<T,std::string>::value,ConstPtr>::type
    make (Context* c,T val) {
      return Const_impl<std::string>(val);
    }

    //TODO make for bit_vector

    template<typename T>
    static inline typename std::enable_if<std::is_convertible<T,Type*>::value,ConstPtr>::type
    make(Context* c,T val) {
      return Const_impl<Type*>(val);
    }

    virtual std::string toString() const = 0;

    //template<typename T>
    //T get() {
    //  
    //  return cast<typename Val2Arg<T>::type>(this)->get();
    //}

};

template<class valTy>
struct Val2Const;

template<>
struct Val2Const<bool> {
  const static Value::ValueKind kind = Value::VK_ConstBool;
};

template<>
struct Val2Const<int> { 
  const static Value::ValueKind kind = Value::VK_ConstInt;
};

template<>
struct Val2Const<std::string> {
  const static Value::ValueKind kind = Value::VK_ConstString;
};

//VAL2TYPEDCONST_SPECIALIZE(CoreIR::Type*,VK_TypeConst);

//T should be bool,int,string,Type
template<typename T>
class TemplatedConst : public Const {
  T value;
  public :
    //typedef T type;
    TemplatedConst(ValueType* type, T value) : Const(Val2Const<T>::kind), value(value) {}
    static bool classof(const Value* v) {return v->getKind()==Val2Const<T>::kind;}
    virtual std::string toString() const {
      ostream
    }
    T get() { return value;}
    bool operator==(const Value& r) const {
      assert(0);
      return false; // TODO
    }
};

using ConstBool = TemplatedConst<bool>;
using ConstInt = TemplatedConst<int>;
using ConstString = TemplatedConst<std::string>;
using ConstType = TemplatedConst<Type*>;

}

#endif
