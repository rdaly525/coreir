#include "coreir-c/coreir.h"
#include "coreir.h"

#include "common-c.hpp"


namespace CoreIR {


extern "C" {

  CORETypeKind COREGetTypeKind(COREType* type) {
    Type* t = rcast<Type*>(type);
    return static_cast<CORETypeKind>(t->getKind());
  }

  COREType* COREFlip(COREType* type) {
    Type* t = rcast<Type*>(type);
    return rcast<COREType*>(t->getFlipped());
  }

  void COREPrintType(COREType* t) {
    rcast<Type*>(t)->print();
  }

  COREType* COREAny(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->Any());
  }
  COREType* COREBitIn(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->BitIn());
  }
  COREType* COREBit(COREContext* c) {
    return rcast<COREType*>(rcast<Context*>(c)->Bit());
  }
  COREType* COREArray(COREContext* c,uint len, COREType* elemType) {
    return rcast<COREType*>(rcast<Context*>(c)->Array(len,rcast<Type*>(elemType)));
  }
  COREType* CORERecord(COREContext* context, void* record_param) {
    return rcast<COREType*>(rcast<Context*>(context)->Record(*rcast<RecordParams*>(record_param)));
  }

  uint COREArrayTypeGetLen(COREType* arrayType) {
    Type* t = rcast<Type*>(arrayType);
    return cast<ArrayType>(t)->getLen();
  }

  COREType* COREArrayTypeGetElemType(COREType* arrayType) {
    Type* t = rcast<Type*>(arrayType);
    Type* elemType = cast<ArrayType>(t)->getElemType();
    return rcast<COREType*>(elemType);
  }
}

}
