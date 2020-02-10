#ifndef IR_RECORD_TYPE_HPP_
#define IR_RECORD_TYPE_HPP_

#include <map>
#include <vector>
#include "type.hpp"

namespace CoreIR{

class RecordType : public Type {
 public:
  // TODO(rsetaluri): Implement this.
  //RecordType(std::shared_ptr<CoreIRContextInterface>* Context, RecordParams _record);
  RecordType(CoreIRContextInterface* Context)
      : Type(Context, TK_Record, DK_Null), Record(), Order() {}

  std::string toString(void) const override;
  int getSize() const override {
    int Size = 0;
    for (auto Field : Record) Size += Field.second->getSize();
    return Size;
  }
  const std::vector<std::string>& getFields() const { return Order; }
  const std::map<std::string, std::shared_ptr<Type>>& getRecord() const {
    return Record;
  }

 private:
  std::map<std::string, std::shared_ptr<Type>> Record;
  std::vector<std::string> Order;
};

}  // namespace CoreIR

#endif  // IR_RECORD_TYPE_HPP_
