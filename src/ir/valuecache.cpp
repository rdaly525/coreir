#include "coreir/ir/value.h"
#include "coreir/ir/valuecache.h"
#include "coreir/ir/context.h"

using namespace std;
namespace CoreIR {

bool BitVectorComp::operator() (const BitVector& l, const BitVector& r) const {
  if (l.bitLength() != r.bitLength()) {
    return l.bitLength() < r.bitLength();
  }

  for (int i = l.bitLength() - 1; i >= 0; i--) {
    auto lv = l.get(i);
    auto rv = r.get(i);

    if (lv.is_binary() && rv.is_binary()) {
      if (lv.binary_value() > rv.binary_value()) {
        return true;
      }
    } else if (lv.is_binary()) {
      return true;
    } else if (rv.is_binary()) {
      return false;
    } else {
      assert(lv.is_unknown() && rv.is_unknown());
    }
  }
  return false;
}

ValueCache::ValueCache(Context* c) : c(c) {
  this->boolTrue = new ConstBool(c->Bool(),true);
  this->boolFalse = new ConstBool(c->Bool(),false);
}

ValueCache::~ValueCache() {
  delete boolTrue;
  delete boolFalse;
  for (auto it : intCache) delete it.second;
  for (auto it : stringCache) delete it.second;
  for (auto it : typeCache) delete it.second;
  for (auto it : moduleCache) delete it.second;
  for (auto it : bvCache) delete it.second;
}

ConstBool* ValueCache::getBool(bool val) {
  return val ? boolTrue : boolFalse;
}

ConstInt* ValueCache::getInt(int val) {
  if (intCache.count(val) ) return intCache[val];
  auto v = new ConstInt(c->Int(),val);
  intCache[val] = v;
  return v;
}

ConstBitVector* ValueCache::getBitVector(BitVector val) {
  if (bvCache.count(val) ) return bvCache[val];
  auto v = new ConstBitVector(c->BitVector(val.bitLength()),val);
  bvCache[val] = v;
  return v;
}

ConstString* ValueCache::getString(string val) {
  if (stringCache.count(val) ) return stringCache[val];
  auto v = new ConstString(c->String(),val);
  stringCache[val] = v;
  return v;
}

ConstCoreIRType* ValueCache::getType(Type* val) {
  if (typeCache.count(val) ) return typeCache[val];
  auto v = new ConstCoreIRType(CoreIRType::make(c),val);
  typeCache[val] = v;
  return v;
}

ConstModule* ValueCache::getModule(Module* val) {
  if (moduleCache.count(val) ) return moduleCache[val];
  auto v = new ConstModule(ModuleType::make(c),val);
  moduleCache[val] = v;
  return v;
}

}
