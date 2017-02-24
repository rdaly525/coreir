## Algebraic structure definition
```
// TODO Metadata

ArgKinds(string* kinds)
Name(string libname, string name)

MetaData(string data, (string key, MetaData m)*)

GenArg = string
       | int
       | float
       | Type
       | Instantiable

GenArgs(GenArg* args)

Type = BitIn | BitOut 
     | Array(number len, Type elemType)
     | Record( Vector((string field,Type fieldType)) args) //Ordered
     | TypeGen(TypeGenDef def, GenArgs args)
     | Named(Name name, Type type)
     | Any
 
TypeGenDef(Name name, ArgKinds kinds, bool flipped, function? fun)



Name(Library lib, string name)
Instantiable = Module(Name name, Type t, MetaData? m, ModuleDef? def)
             | Generator(Name name, Type t, MetaData? m, ArgKinds kinds, function? fun)

//List of modules

ModuleDef(Wire* wires)
Wire(Wireable a, Wireable b)
GeneratorDef(function :: GenArgs -> Module)

Wireable = Interface(ModuleDef container)
         | Instance(ModuleDef container, Instantiable instKind, GenArgs args)
         | Select(Wireable w, string sel)
         //| Strip(Wireable w)
         //| Wrap(Wireable w, Type t)

/////////////////////////////////
//C api
Context newContext();
void deleteContext();

Library newLibrary(string libname);
void registerLib(Context c, Library lib);
Library getGlobal(Context c);

Instantiable newModuleDecl(string name, Type t);
ModuleDef getModuleDef(ModuleDecl m);

Instantiable newGeneratorDecl(string name, ArgKinds kinds, TypeGenDef def);
Instantiable (*genFun)(GenArgs,Type,ArgKinds);
void addGeneratorDef(GeneratorDecl, genFun fun);

Wireable Interface(Context c, ModuleDef context);
Wireable Instance(Context c, ModuleDef context, Instantiable kind, GenArgs args);
Wireable Select(Context c, Wireable w, string sel);
void wire(ModuleDef md, Wireable a, Wireable b);

void libAdd_Instantiable(Library lib, Instantiable i);
Instantiable libGet_Instantiable(Library lib, string name);


//Type Constructors 

Type (*tgenFun)(GenArgs,ArgKinds)
TypeGenDef TypeGenDef(string name, string name_flipped, ArgKinds kinds, tgenFun fun);
void libAdd_TypeGenDef(Library lib, TypeGenDef tgd)
TypeGenDef libGet_TypeGenDef(Library lib, string name)

Type BitIn(Context c);
Type BitOut(Context c);
Type Array(Context c, int n, Type t);
Type Record(Context c, struct pair[]);
Type TypeGen(Context c, TypeGenDef def, GenArgs args);


// Creating GenArgs
GenArg garg_Int(int i);
GenArg garg_String(char* s);
GenArg garg_Float(float f)
GenArg garg_Type(Type t);
GenArg garg_Instantiable(Instantiable i);
GenArgs GenArgs(int len, GenArg* args);

// Creating argKinds
char* argkind_Int();
char* argkind_String();
char* argkind_Float();
char* argkind_Type();
char* argkind_Instantiable();
ArgKinds ArgKinds(int len, char** args);


//Creating/accessing MetaData
MetaData getMetaData_Instantiable(Instantiable i);
void addKeyValue(MetaData m, string key, string value);
int hasKey(MetaData m, string key);
string getValue(MetaData m, string key);
//Probably more

TypeGenDef('std', 'Int', [number], Type def(GenArgs g) return Array(g->i,BitOut))
Int = getTypeGenDef('std','Int')
IntIn = getTypeGenDef('std','Int')
Int5 = TypeGen(Int,5)
InInt5 = TypeGen(IntIn,5)


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
