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
uint CORETypeGetSize(COREType* type) { return rcast<Type*>(type)->getSize(); }

void COREPrintType(COREType* t) { rcast<Type*>(t)->print(); }

COREType* COREBitInOut(COREContext* c) {
  return rcast<COREType*>(rcast<Context*>(c)->BitInOut());
}

COREType* COREBitIn(COREContext* c) {
  return rcast<COREType*>(rcast<Context*>(c)->BitIn());
}
COREType* COREBit(COREContext* c) {
  return rcast<COREType*>(rcast<Context*>(c)->Bit());
}
COREType* COREArray(COREContext* c, uint len, COREType* elemType) {
  return rcast<COREType*>(
    rcast<Context*>(c)->Array(len, rcast<Type*>(elemType)));
}
COREType* CORERecord(COREContext* context, void* record_param) {
  return rcast<COREType*>(
    rcast<Context*>(context)->Record(*rcast<RecordParams*>(record_param)));
}

void CORERecordTypeGetItems(
  COREType* recordType,
  char*** keys,
  COREType*** values,
  int* size) {
  RecordType* type = rcast<RecordType*>(recordType);
  auto const& record = type->getRecord();
  auto const& fields = type->getFields();
  *size = record.size();
  *keys = type->getContext()->newStringArray(*size);
  *values = (COREType**)type->getContext()->newTypeArray(*size);
  int count = 0;
  for (auto field : fields) {
    std::size_t key_length = field.size();
    (*keys)[count] = type->getContext()->newStringBuffer(key_length + 1);
    memcpy((*keys)[count], field.c_str(), key_length + 1);
    (*values)[count] = (COREType*)record.at(field);
    count++;
  }
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

const char* CORENamedTypeToString(COREType* namedType) {
  auto named_type = rcast<NamedType*>(namedType);
  auto str = named_type->toString();
  auto copy = static_cast<char*>(
      named_type->getContext()->getScratchMemory(str.size() + 1));
  strcpy(copy, str.c_str());
  return copy;
}

}  // extern "C"

}  // namespace CoreIR
