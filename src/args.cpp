#ifndef GENARGS_CPP_
#define GENARGS_CPP_

#include "args.hpp"
#include "common.hpp"
#include "error.hpp"
#include "context.hpp"


//TODO might need to be const to make faster
//Also might be better represented virtually and overloade equals/< for each Arg
//Should do a hashing function with unordered map instead

//struct ArgHasher {
//  std::size_t operator()(const Args& ga) const {
//    
//  }
//}


namespace CoreIR {

int Arg::arg2Int() { return ((GenInt*) this)->i; }
string Arg::arg2String() { return ((GenString*) this)->str; }
Type* Arg::arg2Type() { return ((GenType*) this)->t; }

bool ArgInt::operator==(const Arg& r) const {
  if (!Arg::operator==(r)) return false;
  return this->i == static_cast<const ArgInt&>(r).i;
}

bool ArgString::operator==(const Arg& r) const {
  if (!Arg::operator==(r)) return false;
  return this->str == static_cast<const ArgString&>(r).str
}

bool ArgType::operator==(const Arg& r) const {
  if (!Arg::operator==(r)) return false;
  return this->t == static_cast<const ArgType&>(r).t
}

bool checkParams(Args args, Params params) {
  if (args.size() != params.size()) return false;
  for (auto parammap : params) {
    auto arg = args.find(params.first);
    if (arg == args.end()) return false;
    if (!arg.second->isKind(params.second) ) return false;
  }
  return true;
}

}//CoreIR namespace


using namespace CoreIR;

#endif //GENARGS_CPP
