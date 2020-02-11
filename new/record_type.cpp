#include <set>
#include "record_type.hpp"

namespace CoreIR {

// Note that the members are initialized to be empty in the initializer list,
// but filled in the constructor body.
RecordType::RecordType(CoreIRContextInterface* Context,
                       const std::vector<RecordArg>& RecordArgs)
    : Type(Context, TK_Record, DK_Null), Record(), Order() {
  std::set<int> Dirs;
  for (const auto& Field : RecordArgs) {
    // TODO(rsetaluri): Check that the name is valid.
    Record.emplace(Field.first, Field.second);
    Order.push_back(Field.first);
    Dirs.insert(static_cast<int>(Field.second->getDir()));
  }
  // TODO(rsetaluri): Assert no null directions.
  if (Dirs.size() == 1) {
    Dir = static_cast<DirKind>(*(Dirs.begin()));
  } else if (Dirs.size() > 1) {
    Dir = DK_Mixed;
  }
}

std::string RecordType::toString(void) const {
  std::string String = "{";
  const auto Length = Record.size();
  int Index = 0;
  for(auto Name : Order) {
    String += "'" + Name + "': " + Record.at(Name)->toString();
    String += (Index == Length - 1) ? "" : ", ";
    Index++;
  }
  String += "}";
  return String;
}

int RecordType::getSize() const {
  int Size = 0;
  for (auto Field : Record) Size += Field.second->getSize();
  return Size;
}

}  // namespace CoreIR
