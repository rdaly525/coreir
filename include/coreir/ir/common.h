#ifndef COREIR_COMMON_HPP_
#define COREIR_COMMON_HPP_

#include "fwd_declare.h"

//TODO stupid hack
#include "casting/casting.h"

namespace CoreIR {

class ConnectionComp {
  public:
    static bool SPComp(const SelectPath& l, const SelectPath& r);
    bool operator() (const Connection& l, const Connection& r) const;
};

class ValuesComp {
  public:
    bool operator() (const Values& l, const Values& r) const;
};

//TODO Ugly hack to create a sorted connection. Should make my own connection class
Connection connectionCtor(Wireable* a, Wireable* b);

typedef std::set<Connection,ConnectionComp> Connections;

//These are defined in helpers
bool isNumber(std::string s);
bool isPower2(uint n);
std::string Params2Str(Params,bool multi=false);
std::string Values2Str(Values,bool multi=false);
std::string SelectPath2Str(SelectPath path);
std::string Connection2Str(Connection con);
std::string Inst2Str(Instance* inst);

//Checks that the values are of the correct names and types
void checkValuesAreParams(Values args, Params params);

//Checks that all the values are actually constants
void checkValuesAreConst(Values vs);

bool hasChar(const std::string s, char c);

////Used for casting Values, Consts, Args
//template<typename To,typename FromMap>
//std::map<std::string,std::shared_ptr<To>> castMap (FromMap fm) {
//  std::map<std::string,std::shared_ptr<To>> tomap;
//  for (auto fpair : fm) {
//    tomap[fpair.first] = cast<To>(fpair.second);
//  }
//  return tomap;
//}

template<class T> std::string toString(const T& t) {
  std::ostringstream stream;
  stream << t;
  return stream.str();
}

template<typename BackInserter>
BackInserter splitString(const std::string &s, char delim) {
    BackInserter elems;
    std::stringstream ss;
    ss.str(s);
    std::string item;
    while (std::getline(ss, item, delim)) {
      elems.push_back(item);
    }
    return elems;
}

template <class T, class A>
T join(const A &begin, const A &end, const T &t) {
  T result;
  for (A it=begin; it!=end; it++) {
    if (!result.empty())
      result.append(t);
    result.append(*it);
  }
  return result;
}

std::vector<std::string> splitRef(std::string s);


//Does not include
static std::unordered_map<std::string,std::unordered_set<std::string>> coreMap({
  {"unary",{"wire","not","neg"}},
  {"unaryReduce",{"andr","orr","xorr"}},
  {"binary",{
    "add","sub",
    "and","or","xor",
    "shl","lshr","ashr",
    "mul",
    "udiv","urem",
    "sdiv","srem","smod"
  }},
  {"binaryReduce",{
    "eq","neq",
    "slt","sgt","sle","sge",
    "ult","ugt","ule","uge"
  }},
  {"muxType",{"mux"}},
});

void mergeValues(Values& v0, Values v1);

}

#endif

