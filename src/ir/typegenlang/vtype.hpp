#ifndef TYPELANG_VTYPE_HPP_
#define TYPELANG_VTYPE_HPP_

class VTBit : public VType {
  public :
    VTBit() {}
    RetTy eval(Context* c, Args args) {
      return c->Bit();
    }
};

class VTBitIn : public VType {
  public :
    VTBitIn() {}
    Type* eval(Context* c, Args args) {
      return c->BitIn();
    }
};

class VTArray : public VType {
  VInt* len;
  VType* elemtype;
  public :
    VTArray(VInt* len, VType* elemtype) : len(len), elemtype(elemtype) {}
    ~VTArray() {
      delete len;
      delete elemtype;
    }
    Type* eval(Context* c, Args args) {
      return c->Array(len->eval(c,args),elemtype->eval(c,args));
    }
};

class VTRecord : public VType {
  unordered_map<std::string,std::pair<VType*,VBool*>> record;
  public :
    VTRecord(unordered_map<string,std::pair<VType*,VBool*>> record) : record(record) {}
    VTRecord() {}
    ~VTRecord() {
      for (auto field : record) {
        delete field.second.first;
        delete field.second.second;
      }
    }
    void addField(std::string l, VType* vt, VBool* en) {
      ASSERT(record.count(l)==0,"Already added " + l);
      record[l] = {vt,en};
    }
    Type* eval(Context* c, Args args) {
      RecordParams rps;
      for (auto field : record) {
        if (field.second.second->eval(c,args)) {
          rps.push_back({field.first,field.second.first->eval(c,args)});
        }
      }
      return c->Record(rps);
    }
};

#endif
