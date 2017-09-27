#include "coreir/ir/value.h"
#include "coreir/ir/types.h"
//#include "coreir/ir/common.h"

using namespace std;

namespace CoreIR {

bool Arg::operator==(const Value& r) const {
  if (auto rarg = dyn_cast<Arg>(r)) {
    return field == rarg->getField();
  }
  return false;
}

bool operator==(const Values& l, const Values& r) {
  if (l.size() != r.size() ) return false;
  for (auto lmap : l) {
    string field = lmap.first;
    if (r.count(field)==0) return false;
    if (!(*(r[field]) == *(l[field]))) return false;
  }
  return true;
}


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



}

//TODO sketchy because I am overloading a version of unordered_map
size_t std::hash<Values>::operator() (const Values& values) const {
  size_t ret = 0;
  //Need to combine these in an order independent way, so just xor
  for (auto it : args) {
    size_t hash = 0;
    hash_combine(hash,it.first);
    auto arg = it.second;
    switch(arg->getKind()) {
      case Value::VK_Bool : {
        hash_combine(hash,arg->get<bool>());
        break;
      }
      case Value::VK_Int : {
        hash_combine(hash,arg->get<int>());
        break;
      }
      case Value::VK_String : {
        hash_combine(hash,arg->get<string>());
        break;
      }
      case Value::VK_Type : {
        hash_combine(hash,arg->get<Type*>());
        break;
      }
      default : 
        assert(false);
    }
    ret ^= hash;
  }
  return ret;
}
