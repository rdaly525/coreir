#ifndef IR_TYPE_HPP_
#define IR_TYPE_HPP_

#include <string>
#include "contextual.hpp"

namespace CoreIR {

class Type : public Contextual {
 public:
  enum TypeKind {
    TK_Bit = 0,
    TK_BitIn = 1,
    TK_Array = 2,
    TK_Record = 3,
    TK_Named = 4,
    TK_BitInOut = 5
  };
  enum DirKind {
    DK_In = 0,
    DK_Out = 1,
    DK_InOut = 2,
    DK_Mixed = 3,
    DK_Null = 4
  };

  Type(CoreIRContextInterface* Context, TypeKind Kind, DirKind Dir)
      : Contextual(Context), Kind(Kind), Dir(Dir) {}
  virtual ~Type() = default;

  TypeKind getKind() const { return Kind; }
  DirKind getDir() const { return Dir; }
  bool isInput() const { return Dir == DK_In;}
  bool isOutput() const { return Dir == DK_Out; }
  bool isInOut() const { return Dir == DK_InOut; }
  bool isMixed() const { return Dir == DK_Mixed; }
  bool isUnknown() const { return Dir == DK_Null; }
  bool hasInput() const;

  virtual std::string toString() const = 0;
  virtual int getSize() const = 0;

 protected:
  TypeKind Kind;
  DirKind Dir;
};

}  // namespace CoreIR

#endif  // IR_TYPE_HPP_
