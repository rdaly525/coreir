## Types 

```
typedef uint uint32_t;
typedef enum {In,Out} Dir;

Type = UintType(uint bits, Dir dir)
     | IntType(uint bits, Dir dir)
     | FloatType(uint ebits, uint mbits, Dir dir)
     | BoolType(Dir dir)
     | ArrayType(Type baseType, uint len)
     | RecordType(pair<string sel,Type type>* args)
```


## C++ Type Constructors

```
  UintType* Uint(uint bits, Dir dir);
  IntType* Int(uint bits, Dir dir);
  FloatType* Float(uint ebits, uint mbits, Dir dir);
  BoolType* Bool(Dir dir);
  ArrayType* Array(Type* baseType, uint len);
  RecordType* Record(map<string,Type*> recordParams);
  RecordType* AddField(RecordType* record, string key, Type* val);
  Type* Sel(RecordType* record, string key);
  Type* Flip(Type* type);
```

Note: All Types are unique regardless of construction, so they can be checked directly for equality.

## Circuits
```
Circuit = Module
        | Primitive
```
**Circuit:** Black box representing hardware that can be instantiated

**Module:** A circuit which contains instantiations and connections of other circuits

**Primitive:** a 'leaf' circuit containing now interior instantiations

##Wireables
```
Wireable =  Interface 
          | Instance
          | Select
```
**Wireable:** A group of wires (represented by a Type) which resides within a Module

**Interface:** A Wireable representing the interface to the module from the *inside* perspective of the Module. The Interface Type is equal to the flip of the Module type.

**Instance:** A Wireable representing the instantiation of a module within a module.

**Select:** A Wireable which is the record (or Array) selected subgroup of wires from a Wireable.



Module creation
---------------
```
class MagmaIR {
  Module* newModule(stirng name, Type* type);
  Primitive* newPrimitive(string name, Type* type);

class Module {
  Instance* newInstance(string name, Circuit* circuitType);
  Interface* getInterface();
}

class Wireable {
  Select* sel(string key);
  Select* sel(uint idx);
}

MagmaIR* newMagmaIR();
void deleteMagmaIR(MagmaIR* m);
```

##Connecting Wireables

```  
void Connect(Wireable* a, Wireable* b);
```
Connect two Wireables together.
a and b *need* to both be within the same Module. Also a's type needs to be the flip of b's type.


##Example (TODO)

##TODO
TODO NotDepend(PrimitiveWire* a, PrimitiveWire* b); can build fast simulator with this info
//TODO potentially annotate black boxes with dependency graph of inputs to outputs in order to do fast simulate

That is it for the creation of the IR!
Selects are unique and can be checked directly for equality

//Other useful functions (TODO expand)

```
  Type* type(Wireable* wb);
  Type* type(Module m);
  void printpretty(); 
  bool isType(...);
```
