#ifndef COREIR_ARGS_HPP_
#define COREIR_ARGS_HPP_


#include "fwd_declare.h"
#include "casting/casting.h"

namespace CoreIR {

template<class valTy>
struct Val2Arg;

#define VAL2ARG_SPECIALIZE(valtype,argtype) \
template<> \
struct Val2Arg<valtype> { \
  typedef argtype type; \
};

VAL2ARG_SPECIALIZE(bool,ArgBool);
VAL2ARG_SPECIALIZE(int,ArgInt);
VAL2ARG_SPECIALIZE(std::string,ArgString);
VAL2ARG_SPECIALIZE(CoreIR::Type*,ArgType);

#undef VAL2ARG_SPECIALIZE

class Arg {
  Param kind;
  public:
    virtual ~Arg() {}
    Arg(Param kind) : kind(kind) {}
    Param getKind() const { return kind;}
    virtual std::string toString() const = 0;

    template<typename T>
    T get() {
      return cast<typename Val2Arg<T>::type>(this)->get();
    }
  
    virtual bool operator==(const Arg& r) const;
  friend bool operator==(const Args& l, const Args& r);
};

class ArgBool : public Arg {
  bool b;
  public :
    typedef bool type;
    ArgBool(bool b) : Arg(ABOOL), b(b) {}
    static bool classof(const Arg* arg) {return arg->getKind()==ABOOL;}
    std::string toString() const {return b ? "True" : "False";}
    type get() { return b;}
    bool operator==(const Arg& r) const;
};

class ArgInt : public Arg {
  int i;
  public :
    typedef int type;
    ArgInt(int i) : Arg(AINT), i(i) {}
    static bool classof(const Arg* arg) {return arg->getKind()==AINT;}
    std::string toString() const {return std::to_string(i);}
    type get() { return i;}
    bool operator==(const Arg& r) const;
};

class ArgString : public Arg {
  std::string str;
  public :
    typedef const std::string& type;
    ArgString(std::string str) : Arg(ASTRING), str(str) {}
    static bool classof(const Arg* arg) {return arg->getKind()==ASTRING;}
    std::string toString() const { return str;}
    bool operator==(const Arg& r) const;
    type get() { return str;}
};

class ArgType : public Arg {
  Type* t;
  public : 
    typedef Type* type;
    ArgType(Type* t) : Arg(ATYPE), t(t) {}
    static bool classof(const Arg* arg) {return arg->getKind()==ATYPE;}
    std::string toString() const;
    bool operator==(const Arg& r) const;
    type get() { return t;}
};

bool operator==(const Args& l, const Args& r);

//Factory functions for args
//template<typename convertFrom,typename convertTo>
//ArgPtr Const_impl(std::enable_if<std::is_convertible<convertFrom,convertTo>::value,convertFrom>::type val) {
//  return make_shared<convertTo>(val);
//}

//bool
//int
//unsigned int
//string
//..
//
//Const(true)
//Const(5)
//Const(-5)
//Const("literal")



template<typename T> 
ArgPtr Const_impl(T val);

template<>
ArgPtr Const_impl<bool>(bool val);
template<>
ArgPtr Const_impl<int>(int val);
template<>
ArgPtr Const_impl<std::string>(std::string val);
template<>
ArgPtr Const_impl<Type*>(Type* val);

template<typename T>
typename std::enable_if<std::is_same<T,bool>::value,ArgPtr>::type
Const(T val) {
  return Const_impl<bool>(val);
}

template<typename T>
inline typename std::enable_if<!std::is_same<T,bool>::value && std::is_convertible<T,int>::value,ArgPtr>::type
Const(T val) {
  return Const_impl<int>(val);
}

template<typename T>
inline typename std::enable_if<std::is_convertible<T,std::string>::value,ArgPtr>::type
Const(T val) {
  return Const_impl<std::string>(val);
}

template<typename T>
inline typename std::enable_if<std::is_convertible<T,Type*>::value,ArgPtr>::type
Const(T val) {
  return Const_impl<Type*>(val);
}

}//CoreIR namespace


#endif //ARGS_HPP_
