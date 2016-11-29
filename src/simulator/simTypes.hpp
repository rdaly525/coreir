#ifndef SIMTYPES_HPP_
#define SIMTYPES_HPP_

#include <map>


struct BoxedData {
  Type* type; // DO I need this really?
  BoxedData() : type(Int(5)) {}
}

struct BoxedDataInt8 : BoxedData {
  int8_t value;
  
}

struct BoxedDataInt16 : BoxedData {
  int16_t value;
}

struct BoxedDataArray : BoxedData {
  BoxedData** array;
  
}

struct BoxedDataRecord : BoxedData {
  boxedData** record;
}

Type* RV(Type* dataType) {
  return Record({{"data",dataType},{"valid",Int(1)},{"ready",Flip(Int(1))}});
}

BoxedData* createBoxedData(Type*) {
  
}

class simPrimitive;
  DataTypeBits dirty;
  vector<simWire*> outputs; 
  
  virtual void simulate()=0;

}

Type* treeType = Record({{"in",Array(Uint(16),4)},{"out",Flip(Uint(18))}});

void simulate(BoxedData* d,BoxedData* state) {
  uint32_t sum = 0;
  for(int i=0; i<4; ++i) {
    sum += d->R[0]->A[i]->V;
  }
  d->R[1]->V = sum & Mask(18);
}







// Flip flop primitive
Type* FFTypeEn = Record({{"clk",Bit},{"en",Bit},{"D",Uint(16)},{"Q",Uint(16)}});
createState(Uint(16));

void init(BoxedData* state) {
  state->V = 0;
}

void simulate_tick(BoxedData* d,BoxedData* state,BoxedData* dirty) {
  uint8_t clk_dirty = dirty->R[0]->V;
  uint8_t en = d->R[1]->V;
  uint16_t D = d->R[2]->V;
  if(clk_dirty) { //posedge
    if(en) {
      d->R[3]->V = D;
      setDirty(dirty->R[3]);
    }
  }
}

void simulate_comb(BoxedData* d,BoxedData* state) {
  //
}


#endif //SIMTYPES_HPP_
