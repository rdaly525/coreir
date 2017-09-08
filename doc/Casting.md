##Casting

I have the functions `isa<>`, `cast<>`, and `dyn_cast<>` that should fulfill any casting needs. Anyone familiar with writing in llvm should recognize these functions. They work the exact same way as in LLVM.

```

//Use isa to check if something could be casted to some other class.
Type* type = //blah blah
if (isa<RecordType>(type)) {
  cout << This returns a boolean for if it *is a* record type!" << endl
}

//Use Dynamic cast to check whether the cast succeeded.
if (auto arraytype = dyn_cast<ArrayType>(type)) {
  cout << "This works exactly like a dynamic cast" << endl;
  cout << "I am an array type with len = " arraytype->getLen() << endl;
}

//This will assert if the type is not actually a BitType.
BitType* bit = cast<BitType>(type);

//All three functions (isa,cast,dyn_cast) work on normal types, pointers, const types, const pointers. 
BitInType notapointer = cast<BitInType>(*type);

//This does not only work for Types but also works for most of the class hierarchies in coreIR.
/* This includes:
Instantiable
  Generator
  Module

Arg
  ArgBool
  ArgString
  ArgInt
  ArgType

Wireable
  Instance
  Interface
  Select

Pass
  InstancePass
  InstanceVisitorPass
  ModulePass
  NamespacePass
  InstanceGraphPass
*/

Happy casting!

```