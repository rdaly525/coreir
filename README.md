[![Build Status](https://travis-ci.org/rdaly525/coreir.svg?branch=master)](https://travis-ci.org/rdaly525/coreir)


##Tested Compatable compilers:  
  gcc 4.9  
  Apple LLVM version 8.0.0 (clang-800.0.42.1)  


#TODO Add in the APIs  

## Algebraic structure of IR
```
Params(string* kinds)
Name(string libname, string name)

Arg = string
       | int
       | float
       | Type
       | Instantiable

Args(Arg* args)

Type = BitIn | BitOut 
     | Array(number len, Type elemType)
     | Record( Vector((string field,Type fieldType)) args) //Ordered
     | TypeGenInst(TypeGen tg, Args args)
     | Named(Name name, Type type)
     | Any
 
TypeGen(Name name, Params kinds, bool flipped, function? fun)

MetaData(string data, (string key, MetaData m)*)

Instantiable = Module(Name name, Type t, MetaData m, ModuleDef? def)
             | Generator(Name name, Type t, MetaData m, Params kinds, function? fun)

//List of modules

ModuleDef(Wire* wires)
Wire(Wireable a, Wireable b)
GeneratorDef(function :: Args -> Module)

Wireable = Interface(ModuleDef container)
         | Instance(ModuleDef container, Instantiable instKind, Args args)
         | Select(Wireable w, string sel)
         //| Strip(Wireable w)
         //| Wrap(Wireable w, Type t)
```

##C API
TODO convert api to  
ErrType Function(Args);

###Context for coreIR
```
//CoreIR Types: 
//  CoreIRContext

CoreIRContext newContext();
void deleteContext(CoreIRContext c);
```

###Namespaces
Namespaces are similar to that of C++. Each context has a global namespace.

```
//CoreIR Types:
//  Namespace

Namespace newNamespace(string name);
void registerNamespace(Context c, Namespace namespace);
Namespace getGlobal(Context c);  
```

###Generator Args
Generators take a set of well specified arguments. These arguments are string, int, and type. ArgKind specifies the kind of the argument whereas Arg is an instane of the argument itself.

```
//CoreIR Types:
//  ArgKind
//  Params
//  Arg
//  Args

// Creating argKinds
typedef enum {GSTRING,GINT,GTYPE} ArgKind;
Params Params(ArgKind* kinds);

//Creating Args
Arg GInt(int i);
Arg GString(char* s);
//Arg GFloat(float f)
Arg GType(Type t);
// TODO Arg GInstantiable(Instantiable i);
Args Args(int len, Arg* args);

```

###Types
TODO describe the type system

```
//CoreIR Types:
  Type
  TypeGen
  tgenFun

Type (*tgenFun)(Context,Args,Params)
TypeGen TypeGen(string name, string name_flipped, Params kinds, tgenFun fun);
void addTypeGen(Namespace ns, TypeGen tgd)
TypeGen getTypeGen(Namespace ns, string name)

Type BitIn(Context c);
Type BitOut(Context c);
Type Array(Context c, int n, Type t);
Type Record(Context c, <Pairs of string, types> );
Type TypeGenInst(Context c, TypeGen tg, Args args);
//TODO Named
```

###Defining Modules and Generators

```
//CoreIR Types:
//  Module
//  ModuleDef
//  Generator

Module newModuleDecl(Context c, string name, Type* t);
p
ModuleDef newModuleDef(Module* m);
void addModuleDef(Module* module, ModuleDef* moduledef);
void addModule(Namespae ns, Module m);
Module getModule(Namespace ns, string name);

Generator newGeneratorDecl(Context c, string name, Params kinds, TypeGen tg);
Module (*genFun)(Context,Type,Args,Params);
void addGeneratorDef(Generator decl, genFun fun);

void addGenerator(Namespace ns, Generator g);
Generator getGenerator(Namespace lib, string name);
```

###Wiring things together
```
Wireable Interface(Context c, ModuleDef context);
Wireable InstanceGenerator(Context c, ModuleDef context, Module instkind);
Wireable InstanceModule(Context c, ModuleDef context, Generator instkind, Args args);
Wireable Select(Context c, Wireable w, string sel);
void wire(ModuleDef md, Wireable a, Wireable b);
```

###Metadata
TODO

```
//Creating/accessing MetaData
MetaData getMetaData_Instantiable(Instantiable i);
void addKeyValue(MetaData m, string key, string value);
int hasKey(MetaData m, string key);
string getValue(MetaData m, string key);
//Probably more
```

###Example
```
TypeGenDef('std', 'Int', [number], Type def(Args g) return Array(g->i,BitOut))
Int = getTypeGenDef('std','Int')
IntIn = getTypeGenDef('std','Int')
Int5 = TypeGen(Int,5)
InInt5 = TypeGen(IntIn,5)
```

## Useful functions

###IR I/O
```
//Inputs JSON coreIR file
Namespace File2CoreIR(string fileName);

void Instantiable2File(Instantiable i, string fileName);
void Namespace2File(Namespace lib, string fileName);
```

###IR creation sugar
```


```

###IR -> IR compilation passes
```
//Resolves a combination of templates,generators,type defs, instantiable defs
Instantiable resolve(Instantiable, options);
//Options
  -Instantiation recurse Depth (0-ALL)
  -Generator recurse Depth(0-All)
  -Run/dont run Generators from <List>
  -Template recurse Depth(0-All)
  -Run/Dont run Templates from <List>
  -Erase named types Depth (0-All)


Instantiable flatten(Instantiable,Options);
//Options
  Flatten types recurse Depth (0-ALL)
  Flatten Module recurse Depth (0-ALL)

//Writes verilog to filename 
void verilog(string filename, Instantiable);
```


### IR -> Bool checking Passes
```
Bool checkResolved(Instantiable,options);
//Options
  -Check generators
  -Check templates
  -Check instantiation defs
  -Check type defs

//Verifies that all Selects are valid and that all Wire(a,b) => a.type==flip(b.type)
Bool typeCheck(Instantiable,options);
//Options
  -Strict named-type check?
  
Bool checkWires(Instantiable,options);
//Options
  -Check unconnected outputs
```

###Helpful graph traversing functions
```
//Get functions 
```
#TODO Below this point

## Types 
```
Example of a Ready-valid handshake type.

Int = GenInt()
Type* rv = Record({
  {'data',Int(32)},
  {'valid',Int(1)},
  {'ready',Flip(Int(1))}
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

Note: This is a structural type system so they can be checked directly for equality.

## Instantiables
```
Instantiable = ModuleDef(string name, Type t, Wireing* wireings)
             | ModuleDecl(string library, string name)
             | ModuleGenDef(string name, function genfun, genarg_t* argtypes)
             | ModuleGenDecl(string library, string name)

```

**Instantaibles** are circuits that can be instantiated within a module.

**ModuleDef:** Defintion of a Module/circuit. This is a graph descritpion of Instantiables (nodes) and how everything is wired together (edges)  
**ModuleDecl:** Declaration of a Module. Does not need a definition. Will resolve to a definition in linking.  
**ModuleGenDef:** Definition of a moduleGen. has a function of type: ModuleDef* (fun*)(NameSpace*,Args*). This function will generate a new ModuleDef when given Args.  
**ModuleGenDecl:** Declaration of a moduleGen. Does not need a definition, will resolve to a definition in linking.



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
  void addModuleGenDef(ModuleGenDef* gen);

class CoreIR 
  NameSpace registerLib(string libname);
  void addModuleDecl(ModuleDecl* mod);
  void addModuleGenDecl(ModuleGenDecl* gen);
```


##Example (TODO)


