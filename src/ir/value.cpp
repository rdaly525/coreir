#include "coreir/ir/context.h"
#include "coreir/ir/common.h"
#include "coreir/ir/value.h"
#include "coreir/ir/types.h"
#include "coreir/ir/dynamic_bit_vector.h"

using namespace std;

namespace CoreIR {

bool Value::operator==(const Value& r) const {
  return (r.getKind() == this->getKind()) && (this->getValueType() == r.getValueType());
}

bool Value::operator<(const Value& r) const {
  return this->getKind() < r.getKind();
}

bool Arg::operator==(const Value& r) const {
  if (!Value::operator==(r)) return false;
  return field == static_cast<const Arg&>(r).getField();
}

bool Arg::operator<(const Value& r) const {
  if (!Value::operator==(r)) return field < static_cast<const Arg&>(r).getField();
  return false;
}

#define TSTAMP(utype) \
template<> \
bool TemplatedConst<utype>::operator==(const Value& r) const { \
  if (!Value::operator==(r)) return false; \
  return this->get() == static_cast<const TemplatedConst<utype>&>(r).get(); \
} \
template<> \
bool TemplatedConst<utype>::operator<(const Value& r) const { \
  if (Value::operator==(r)) return Value::operator<(r); \
  return this->get() < static_cast<const TemplatedConst<utype>&>(r).get(); \
} \

TSTAMP(bool)
TSTAMP(int)
TSTAMP(BitVector)
TSTAMP(std::string)
TSTAMP(Type*)

#undef TSTAMP

bool operator==(const Values& l, const Values& r) {
  if (l.size() != r.size() ) return false;
  for (auto lpair : l) {
    string field = lpair.first;
    auto rpair = r.find(field);
    if (rpair == r.end()) return false;
    if (!(*(rpair->second) == *(lpair.second))) return false;
  }
  return true;
}

bool operator==(const Consts& l, const Consts& r) {
  return castMap<Value>(l) == castMap<Value>(r);
}

bool ValuesComp::operator() (const Values& l, const Values& r) const {
  if (l.size() != r.size()) return l.size() < r.size();
  auto itl = l.begin();
  auto itr = r.begin();
  for ( ; itl!=l.end(); ++itl, ++itr) {
    if (itl->first != itr->first) return itl->first < itr->first;
    if (itl->second != itr->second) return itl->second < itr->second;
  }
  return false;
}

bool ConstsComp::operator() (const Consts& l, const Consts& r) const {
  ValuesComp vc;
  return vc(castMap<Value>(l),castMap<Value>(r));
}

template<typename T>
ConstPtr Const_impl2(ValueType* type,T val) {
  return Underlying2ValueType<T>::type::make(type,val);
}

template<>
ConstPtr Const_impl<bool>(Context* c,bool val) {
  return ConstBool::make(c->Bool(),val);   
}

template<>
ConstPtr Const_impl<int>(Context* c,int val) {
  return Const_impl2<int>(c->Int(),val);   
}

template<>
ConstPtr Const_impl<BitVector>(Context* c,BitVector val) {
  return Const_impl2<BitVector>(c->BitVector(val.bitLength()),val);   
}

template<>
ConstPtr Const_impl<std::string>(Context* c,std::string val) {
  return Const_impl2<std::string>(c->String(),val);   
}

template<>
ConstPtr Const_impl<Type*>(Context* c,Type* val) {
  return Const_impl2<Type*>(c->CoreIRType(),val);   
}


template<>
string TemplatedConst<bool>::toString() const {
  return vtype->toString() + "(" + (value ? "True" : "False") + ")";
}

template<>
string TemplatedConst<int>::toString() const {
  return vtype->toString() + "(" + to_string(value) + ")";
}

template<>
string TemplatedConst<BitVector>::toString() const {
  return vtype->toString() + "(" + to_string(value.to_type<int>()) + ")";
}

template<>
string TemplatedConst<std::string>::toString() const {
  return vtype->toString() + "(" + value + ")";
}

template<>
string TemplatedConst<Type*>::toString() const {
  return vtype->toString() + "(" + value->toString() + ")";
}

}

//using namespace CoreIR;
////TODO sketchy because I am overloading a version of unordered_map
//size_t std::hash<Values>::operator() (const Values& values) const {
//  size_t ret = 0;
//  //Need to combine these in an order independent way, so just xor
//  for (auto it : values) {
//    size_t hash = 0;
//    hash_combine(hash,it.first);
//    auto arg = it.second;
//    switch(arg->getKind()) {
//      case Value::VK_Bool : {
//        hash_combine(hash,arg->get<bool>());
//        break;
//      }
//      case Value::VK_Int : {
//        hash_combine(hash,arg->get<int>());
//        break;
//      }
//      case Value::VK_String : {
//        hash_combine(hash,arg->get<string>());
//        break;
//      }
//      case Value::VK_Type : {
//        hash_combine(hash,arg->get<Type*>());
//        break;
//      }
//      default : 
//        assert(false);
//    }
//    ret ^= hash;
//  }
//  return ret;
//}
