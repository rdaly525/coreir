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

//class Instantiable;
//class ArgInst : Arg {
//  Instantiable* i;
//  ArgInst(Instantiable* i) : Arg(AINST), i(i) {}
//};


//bool checkArgs(Args args, Params params);

}//CoreIR namespace


#endif //ARGS_HPP_
