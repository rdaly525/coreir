###How to read this:  
Anything in <> should be filled in by user as a string  
Anything not in quotes is a json format defined below  
any key followed by a ? means it is optional  

```
//What is in the json file
{<namespaceName>:Namespace, ...}


//Definitions

Namespace={
  "namedtypes"? : {<name>: NamedType, ...}
  "namedtypegens"? : {<name>: NamedTypeGen, ...}
  "modules"? :{<name>:Module, ...},
  "generators"? :{<name>:Generator, ...}
}

Type = "BitIn" 
     | "Bit" 
     | ["Array", <N>, Type] 
     | ["Record", [<key>:Type,...] ] 
     | ["Named",NamedRef, Args?]

//This could be referring a type, module, or generator
NamedRef = "<namespaceName>.<name>"

NamedType = {"flippedname":<name>,"rawtype":Type}
NamedTypeGen = {"flippedname"?:<name>,"genparams":Parameter}

//Note if there are no instances and no connections, this is a declaration
Module = {
  "type":Type,
  "configparams"?:Parameter,
  "defaultconfigargs"?:Args,
  "instances"?:{<instname>:Instance,...},
  "connections"?: Connection[]
}

Generator = {
  "typegen":NamedRef
  "genparams":Parameters,
  "defaultgenargs"?:Args,
  "configparams"?:Parameters,
  "defaultconfigargs"?:Args,
}

Instance = {
  "modref"?:NamedRef,
  "genref"?:NamedRef,
  "genargs"?:Args,
  "configargs"?:Args
}

Connection = [Wireable, Wireable]

//accesses instname.a.b If "instname" is "self" then this is the module's interface.
//Note: a,b can be digits representing an index. 
Wireable = "<instname>,<a>,<b>,..."

Parameters = {<key>:ParameterType,...}
ParameterType = "Bool" | "Uint" | "Int" | "String" | "Type" | //NYI "Instantiatable"

Args = {<key>:ArgsValue}
ArgsValue = <Bool> | <Number> | <string> | Type | //NYI InstantiatableReference

```
