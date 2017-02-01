## Algebraic structure definition
```
// TODO Metadata

Signature(string* argTypes)
Name(string libname, string name)

module Type {
  
  Dir = In | Out | Inout
  
  Type = Bit(Dir? dir)
       | Array(Type elemType, number len)
       | Record( (string? field,Type fieldType)* args) //Ordered
       | Named(Name name, TypeDef? def)
       | TypeGenerator(Name name, Signature? signature, TemplateDef? def, TemplateArg? arg)
 
  NamedDef(Type raw, Dir? dir)
  TemplateDef(templateFun :: TemplateArgType -> Type)

  ArgType = string
          | number
          | Type

  TemplateArg(ArgType* args)
}

Instantiable = Module(Name name, Type.Type? t, ModuleDef? def)
             | Generator(Name name, Signature? signature, GeneratorDef? def)

Wire(Wireable a, Wireable b)
ModuleDef(Type.Type t, Wire* )
GeneratorDef(genFun :: ArgType -> Instantiable)

ArgType = string
        | number
        | Type
        | Instantiable

Wireable = Interface(ModuleDef container)
         | Instance(ModuleDef container, Instantiable instType, string? instName, GeneratorArg? arg)
         | Select(Wireable w, string sel)

GeneratorArg(ArgType* args)

/////////////////////////////////

// Not quite part of the IR

Library(string libname)

AddInstantiable(Library lib,Instantiable i)
AddType(Library lib, Type t)

Context(Library? global)
RegisterLib(Context c, Library lib)


```


## Useful functions

###IR I/O
```
//Inputs JSON coreIR file
Library File2CoreIR(string fileName);

void Instantiable2File(Instantiable i, string fileName);
void Library2File(Library lib, string fileName);
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
**ModuleGenDef:** Definition of a moduleGen. has a function of type: ModuleDef* (fun*)(NameSpace*,GenArgs*). This function will generate a new ModuleDef when given GenArgs.  
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

##Other useful functions (TODO expand)
