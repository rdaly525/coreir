
/* 
WireBundle = Interface 
           | Instance
           | Select

Type = UintType  
     | IntType
     | FloatType 
     | BoolType 
     | ArrayType 
     | RecordType
*/

typedef uint uint32_t;
typedef enum {In,Out} Dir;
typedef string char[];

// Type Constructors
UintType* Uint(uint bits, Dir dir);
IntType* Int(uint bits, Dir dir);
FloatType* Float(uint ebits, uint mbits, Dir dir);
BoolType* Bool(Dir dir);
ArrayType* Array(Type* baseType, uint len);
RecordType* Record(string key, Type* val,...);
RecordType* AddField(RecordType* record, string key, Type* val);

Type* Select(RecordType* iface, string key);
Type* Flip(Type* type);

//Typeinfo
string getType(Type* type);
uint getBits(Type* type);

//Module creation
Module* newModule(string name,Type* type);
void addMetadataToModule(Module* mod, TODO);
Interface* getInterface(Module* module);
Instance* newInstance(string name, Module* instanceIn, Module* instanceFrom);
Select* Select(string key, WireBundle* wirebundle);
Index* Index(uint idx, WireBundle* wirebundle);
void Connect(WireBundle* a, WireBundle* b);



