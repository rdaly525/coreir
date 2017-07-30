class VTBit : public VType {
  public :
    VTBit() {}
    Type* eval(Context* c, Args args) {
      return c->Bit();
    }
};

class VTBitIn : public VType {
  VTBitIn() {}
  Type* eval(Context* c, Args args) {
    return c->BitIn();
  }
};

class VTArray : public VType {
  VInt* len;
  VType* elemtype;
  VTArray(VInt* len, VType* elemtype) : len(len), elemtype(elemtype) {}
  Type* eval(Context* c, Args args) {
    return c->Array(len->eval(),elemtype->eval());
  }
};

class VTRecord : public VType {
  unordered_map<string,VType> types;
  unordered_map<string,VBool> enables;
};
