## Algebraic structure definition
```
Dir = In 
    | Out
    // NYI | Inout

Type = IntType(uint bits, Dir dir)
     | ArrayType(Type baseType, uint len)
     | RecordType( (string sel,Type type)* args)
     //NYI | NamedType(string name, Type t, Dir dir)

Instantiable = ModuleDef(string name, Type t, Wireing* wireings)
             | ModuleDecl(string library, string name)
             | GeneratorDef(string name, function genfun, genarg_t* argtypes)
             | GeneratorDecl(string library, string name)

Wireable =  Interface(ModuleDef container)
          | Instance(ModuleDef container, string instname, Instantiable def)
          | Select(Wireable w, string s)

Wireing(Wireable a, Wireable b)

genarg_t = string
         | int
         | ModuleDef
          //NYI | Type

GenArg = GenString(string s)
       | GenInt(int i)
       | GenMod(ModuleDef mod)
       // NYI | GenType(Type t)

GenArgs(genarg_t* argtypes, GenArg* args)

```

## Types 
```
Example of a Ready-valid handshake type.

Type* rv = Record({
  {'data',Int(32,Out)},
  {'valid',Int(1,Out)},
  {'ready',Int(1,In)}
});

```


## C++ Type Constructors

```
  IntType* Int(uint bits, Dir dir);
  ArrayType* Array(Type* baseType, uint len);
  RecordType* Record(map<string,Type*> recordParams);
  RecordType* AddField(RecordType* record, string key, Type* val);
  Type* Sel(RecordType* record, string key);
  Type* Flip(Type* type);
```

Note: All Types are unique regardless of construction, so they can be checked directly for equality.

## Instantiables
```
Instantiable = ModuleDef(string name, Type t, Wireing* wireings)
             | ModuleDecl(string library, string name)
             | GeneratorDef(string name, function genfun, genarg_t* argtypes)
             | GeneratorDecl(string library, string name)

```

**Instantaibles** are circuits that can be instantiated within a module.

**ModuleDef:** Defintion of a Module/circuit. This is a graph descritpion of Instantiables (nodes) and how everything is wired together (edges)  
**ModuleDecl:** Declaration of a Module. Does not need a definition. Will resolve to a definition in linking.  
**GeneratorDef:** Definition of a generator. has a function of type: ModuleDef* (fun*)(NameSpace*,GenArgs*). This function will generate a new ModuleDef when given GenArgs.  
**GeneratorDecl:** Declaration of a generator. Does not need a definition, will resolve to a definition in linking.



##Wireables
```
Wireable =  Interface(ModuleDef container)
          | Instance(ModuleDef container, string instname, Instantiable def)
          | Select(Wireable w, string s)

Wireing(Wireable a, Wireable b)
```

**Wireable:** A group of wires which resides within a Module

**Interface:** A Wireable representing the interface to the module from the *inside* perspective of the Module. The Interface Type will be equal to the flip of the Module type.  
**Instance:** A Wireable representing the instantiation of an Instantiable within a moduleDef.  
**Select:** A Wireable which is the record (or Array) selected subgroup of wires from a Wireable.  
**Wiring:** Connection two wireables together. The types of these wireables should be opposite. a.type == Flip(b.type)


Module creation
---------------
```
class NameSpace
  void addModuleDef(ModuleDef* mod);
  void addGeneratorDef(GeneratorDef* gen);

class CoreIR 
  NameSpace registerLib(string libname);
  void addModuleDecl(ModuleDecl* mod);
  void addGeneratorDecl(GeneratorDecl* gen);
```


##Example (TODO)

##Other useful functions (TODO expand)
