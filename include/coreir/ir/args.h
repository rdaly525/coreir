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
ArgPtr Const_impl<bool>(bool val) {
  return std::make_shared<ArgBool>(val);
}

template<>
ArgPtr Const_impl<int>(int val) {
  return std::make_shared<ArgInt>(val);
}

template<>
ArgPtr Const_impl<std::string>(std::string val) {
  return std::make_shared<ArgString>(val);
}

template<>
ArgPtr Const_impl<Type*>(Type* val) {
  return std::make_shared<ArgType>(val);
}

template<typename T>
struct always_false : std::false_type {};

template<typename T>
ArgPtr Const(T val) {
  static_assert(always_false<T>::value,"Must Specialize");
}

template<>
ArgPtr Const<bool>(bool val) {
  return Const_impl<bool>(val);
}

//template<typename T,typename std::enable_if<std::is_same<T,bool>::value,int>::type=0>
//ArgPtr Const(T val) {
//  return Const_impl<bool>(val);
//}

template<typename T,typename std::enable_if<!std::is_same<T,bool>::value && std::is_convertible<T,int>::value,int>::type=0>
ArgPtr Const(T val) {
  return Const_impl<int>(val);
}

//template<>
//ArgPtr Const<const char*>(const char* val) {
//  return Const(std::string(val));
//}


//ArgPtr Const(bool val);
//ArgPtr Const(int val);
//ArgPtr Const(unsigned int val);
//ArgPtr Const(std::string val);
//ArgPtr Const(const char* val) ;
//ArgPtr Const(Type* val);
  
//
//template<typename T, typename ConvertT>
//ArgPtr Const_impl(T val) {
//  return std::make_shared<typename Val2Arg<ConvertT>::type>(val);
//}
//
//template<typename T, typename ConvertT>
//ArgPtr Const(T val);
//
//template<> 
//ArgPtr Const<bool,bool>(bool val) {
//  return Const_impl<bool,bool>(val);
//}
//
//template<typename T,typename std::enable_if<std::is_convertible<T,int>::value,int>::type=0>
//ArgPtr Const<T,int>(T val) {
//  return Const_impl<T,int>(val);
//}
//
//template<typename T,typename std::enable_if<std::is_convertible<T,std::string>::value,int>::type=0>
//ArgPtr Const<T,std::string>(T val) {
//  return Const_impl<T,std::string>(val);
//}
//


//
//template<typename T>
//ArgPtr Const(T val) {
//  return Const_impl<T,T>(val);
//}
//
//template<T>
//ArgPtr Const(T val) {
//  return Const_impl

//template<typename T, ConverT, typename std::enable_if<std::is_same<T,bool>::value,int>::type=0>
//ArgPtr Const(T val);
//
//template<>
//ArgPtr Const<bool>(bool val) {
//  return std::make_shared<ArgBool>(val);
//}
//
//template<typename T,typename std::enable_if<!std::is_same<T,bool>::value && std::is_convertible<T,int>::value,int>::type=0>
//ArgPtr Const(T val) {
//  return std::make_shared<ArgInt>(val);
//}

//template<typename T,typename std::enable_if<std::is_convertible<T,std::string>::value,int>::type=0>
//ArgPtr Const(T val) {
//  return std::make_shared<ArgString>(val);
//}
//
//template<typename T,typename std::enable_if<std::is_convertible<T,Type*>::value,int>::type=0>
//ArgPtr Const(T val) {
//  return std::make_shared<ArgType>(val);
//}



//std::shared_ptr<Arg> Const(bool b) ;
//std::shared_ptr<Arg> Const(int i);
//std::shared_ptr<Arg> Const(std::string s);
//std::shared_ptr<Arg> Const(Type* t);

//class Instantiable;
//class ArgInst : Arg {
//  Instantiable* i;
//  ArgInst(Instantiable* i) : Arg(AINST), i(i) {}
//};


//bool checkArgs(Args args, Params params);

}//CoreIR namespace


#endif //ARGS_HPP_
