#ifndef ARGS_HPP_
#define ARGS_HPP_


#include "types.hpp"
#include "common.hpp"
#include <cassert>
#include "json.hpp"
#include "casting/casting.hpp"

using json = nlohmann::json;
using namespace std;

//class Params {
//  unordered_map<string,Param> dict;
//  Params(unordered_map<string,Param> dict) : dict(dict) {}
//  Param operator[](const string& key) {
//    //What should I do if this is not valid?
//    return dict[key];
//  }
//}

namespace CoreIR {

class Arg {
  Param kind;
  public:
    virtual ~Arg() {}
    Arg(Param kind) : kind(kind) {}
    Param getKind() const { return kind;}
    virtual string toString() const = 0;

    template<typename T>
    typename T::type get() {
      return cast<T>(this)->get();
    }
  
    virtual json toJson()=0;
    virtual bool operator==(const Arg& r) const {
      return r.getKind() == this->kind;
    }
  friend bool operator==(const Args& l, const Args& r);
};

class ArgBool : public Arg {
  int b;
  public :
    typedef bool type;
    ArgBool(bool b) : Arg(ABOOL), b(b) {}
    static bool classof(const Arg* arg) {return arg->getKind()==ABOOL;}
    string toString() const {return b ? "True" : "False";}
    type get() { return b;}
    bool operator==(const Arg& r) const;
    json toJson();
};

class ArgInt : public Arg {
  int i;
  public :
    typedef int type;
    ArgInt(int i) : Arg(AINT), i(i) {}
    static bool classof(const Arg* arg) {return arg->getKind()==AINT;}
    string toString() const {return to_string(i);}
    type get() { return i;}
    bool operator==(const Arg& r) const;
    json toJson();
};

class ArgString : public Arg {
  string str;
  public :
    typedef const string& type;
    ArgString(string str) : Arg(ASTRING), str(str) {}
    static bool classof(const Arg* arg) {return arg->getKind()==ASTRING;}
    string toString() const { return str;}
    bool operator==(const Arg& r) const;
    json toJson();
    type get() { return str;}
};

class ArgType : public Arg {
  Type* t;
  public : 
    typedef Type* type;
    ArgType(Type* t) : Arg(ATYPE), t(t) {}
    static bool classof(const Arg* arg) {return arg->getKind()==ATYPE;}
    string toString() const;
    bool operator==(const Arg& r) const;
    json toJson();
    type get() { return t;}
};

//class Instantiable;
//class ArgInst : Arg {
//  Instantiable* i;
//  ArgInst(Instantiable* i) : Arg(AINST), i(i) {}
//};


bool checkArgs(Args args, Params params);

}//CoreIR namespace


#endif //ARGS_HPP_
