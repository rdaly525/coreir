  typedef uint uint32_t;
  typedef enum {In,Out} Dir;

Here are all the Types in algebraic form 
Type = UintType(uint bits, Dir dir)
     | IntType(uint bits, Dir dir)
     | FloatType(uint ebits, uint mbits, Dir dir)
     | BoolType(Dir dir)
     | ArrayType(Type baseType, uint len)
     | RecordType(pair<string sel,Type type>* args)


C++ Type Constructors

  UintType* Uint(uint bits, Dir dir);
  IntType* Int(uint bits, Dir dir);
  FloatType* Float(uint ebits, uint mbits, Dir dir);
  BoolType* Bool(Dir dir);
  ArrayType* Array(Type* baseType, uint len);
  RecordType* Record(map<string,Type*> recordParams);
  RecordType* AddField(RecordType* record, string key, Type* val);
  Type* Sel(RecordType* record, string key);
  Type* Flip(Type* type);

Note: All Types are unique regardless of construction, so they can be checked directly for equality.


Circuit: Black box representing hardware that can be instantiated
Module: a circuit which contains instantiations and connections of other circuits
Primitive: a 'leaf' circuit containing now interior instantiations

  Circuit = Module
          | Primitive


Wirebundle: A group of wires (represented by a Type) which resides within a Module
Interface: a WireBundle representing the interface to the module from the *inside* perspective of the Module. The Interface Type is equal to the flip of the Module type.
Instance: a WireBundle representing the instantiation of a module within a module.
Select: a WireBundle which is the record selected subgroup of wires from a WireBundle.
Index: a WireBundle which is the array indexed subgroup of wires from a WireBundle

  WireBundle = Interface 
             | Instance
             | Select
             | Index


Module creation
---------------

  class Primitive {
    Primitive(string name, Type* type, verilogRef?)
  }

  class Module {
    Module(string name, Type* type);
    Instance* newInstance(string name, Circuit* circuitType);
    Interface* getInterface();
  }

  class WireBundle {
    Select* sel(string key);
    Index* idx(uint idx);
  }

Connect two WireBundles together.
a and b *need* to be within the same Module
assert(type(a) == flip(type(b)))
  
  void Connect(WireBundle* a, WireBundle* b);

That is it for the creation of the IR!
Selects and Indexes are unique and can be checked directly for equality

//Other useful functions (TODO expand)

  Type* type(WireBundle* wb);
  Type* type(Module m);
  void printpretty(); 
  bool isType(...);
