class simWire {
  string name
  BaseType* type
  simInstance* inst;

  simWire* source;
  vector<simWire*> sinks;
  
  simWire* skipSource;
  vector<simWire*> skipSinks;

  bool dirty;
  wireValue* value;
};

struct simPrimitive{
  void (*updateOutput)(BoxedData*,BoxedData*,DirtyBits*);
  Type* stateType;
  void (*init)(BoxedData*);
  void (*updateState)(BoxedData*,BoxedData*,DirtyBits*);
  simPrimitive(
    void (*updateOutput)(BoxedData*,BoxedData*,DirtyBits*)
    Type* stateType=nullptr,
    void (*init)(BoxedData*)=nullptr,
    void (*updateState)(BoxedData*,BoxedData*,DirtyBits*)=nullptr,
  ) : stateType(stateType), init(init), updateState(updateState), updateOutput(updateOutput) {}
};

struct BoxedData {
  BoxedData** A;
}

struct BDInt16 : BoxedData {
  
}

//TODO potetially have 'sel' as a function pointer
Type* add4_N16 = Record({{"in",Array(Uint(16),4)},{"out",Flip(Uint(16))}});

void updateOutput_add4_N16(BoxedData* iface,BoxedData* state,DirtyBits* db) {
  uint16_t sum = 0;
  for(int i=0; i<4; ++i) {
    sum += ((BDInt8)iface->A[0]->A[i])->V;
  }
  if ( ((BDInt16)iface->R[1])->V !=sum) {
    setDirty(db->A[1]);
    ((BDInt16)iface->A[1])->V = sum;
  }
  // Alternatively could have checked if inputs were dirty
}
simPrimitive add4_N16_simPrim(updateOutput_add4_N16);


// Flip flop primitive
Type* FFEn_N16 = Record({{"clk",Bit},{"en",Bit},{"D",Uint(16)},{"Q",Uint(16)}});

void init_FFEn_N16(BoxedData* state) {
  state->V = 0;
}

void updateState_FFEn_N16(const BoxedData* iface,BoxedData* state,BoxedData* dirty) {
  bool en = iface->R[1]->V;
  uint16_t D = iface->R[2]->V;
  if(en) state->V = D;
}

void updateOutput_FFEn_N16(BoxedData* iface,const BoxedData* state,BoxedData* dirty) {
  //Can assume clock is dirty
  //uint8_t clk_dirty = dirty->R[0]->V;
  if (iface->R[3]->V != state->V) {
  iface->R[3]->V = state->V;
  setDirty(dirty->R[3]);
}
simPrimitive FFEn_N16_simPrim(updateOutput_FFEn_N16,Int(16),
