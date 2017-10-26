#include "coreir/ir/args.h"
#include "coreir/ir/types.h"
#include "coreir/ir/common.h"

using namespace std;

namespace CoreIR {

template<typename T>
ArgPtr Const_impl2(T val) {
  return std::make_shared<typename Val2Arg<T>::type>(val);
}

template<>
ArgPtr Const_impl<bool>(bool val) {
  return Const_impl2<bool>(val);   
}

template<>
ArgPtr Const_impl<int>(int val) {
  return Const_impl2<int>(val);   
}

template<>
ArgPtr Const_impl<std::string>(std::string val) {
  return Const_impl2<std::string>(val);   
}

template<>
ArgPtr Const_impl<Type*>(Type* val) {
  return Const_impl2<Type*>(val);   
}

bool Arg::operator==(const Arg& r) const {
  return r.getKind() == this->kind;
}

bool ArgBool::operator==(const Arg& r) const {
  if (!Arg::operator==(r)) return false;
  return this->b == static_cast<const ArgBool&>(r).b;
}

bool ArgInt::operator==(const Arg& r) const {
  if (!Arg::operator==(r)) return false;
  return this->i == static_cast<const ArgInt&>(r).i;
}

bool ArgString::operator==(const Arg& r) const {
  if (!Arg::operator==(r)) return false;
  return this->str == static_cast<const ArgString&>(r).str;
}

bool ArgType::operator==(const Arg& r) const {
  if (!Arg::operator==(r)) return false;
  return this->t == static_cast<const ArgType&>(r).t;
}
string ArgType::toString() const { return t->toString();}

bool operator==(const Args& l, const Args& r) {
  if (l.size() != r.size() ) return false;
  for (auto largmap : l) {
    auto rargmap = r.find(largmap.first);
    if (rargmap == r.end() ) return false;
    if (!(*(rargmap->second) == *(largmap.second))) return false;
  }
  return true;
}

}//CoreIR namespace

using namespace CoreIR;

//TODO sketchy because I am overloading a version of unordered_map
size_t std::hash<Args>::operator() (const Args& args) const {
  size_t ret = 0;
  //Need to combine these in an order independent way, so just xor
  for (auto it : args) {
    size_t hash = 0;
    hash_combine(hash,it.first);
    auto arg = it.second;
    switch(arg->getKind()) {
      case ASTRING : {
        string arg_s = arg->get<string>();
        hash_combine(hash,arg_s);
        break;
      }
      case ABOOL : {
        bool arg_b = arg->get<bool>();
        hash_combine(hash,arg_b);
        break;
      }
      case AINT : {
        int arg_i = arg->get<int>();
        hash_combine(hash,arg_i);
        break;
      }
      case ATYPE : {
        Type* arg_t = arg->get<Type*>();
        hash_combine(hash,arg_t);
        break;
      }
      default : 
        assert(false);
    }
    ret ^= hash;
  }
  return ret;
}
