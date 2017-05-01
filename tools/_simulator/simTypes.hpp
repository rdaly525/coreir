#ifndef SIMTYPES_HPP_
#define SIMTYPES_HPP_

#include <map>


struct BoxedData {
  Type* type; // DO I need this really?
  BoxedData() : type(Int(5)) {}
}

struct BoxedDataInt8 : BoxedData {
  int8_t V;
  
}

struct BoxedDataArray : BoxedData {
  BoxedData** A;
  
}

struct BoxedDataRecord : BoxedData {
  boxedData** R;
}

BoxedData* createBoxedData(Type*) {
  
}


#endif //SIMTYPES_HPP_
