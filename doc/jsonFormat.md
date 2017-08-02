###How to read this:  
Anything in <> should be filled in by user  
Anything not in quotes is a json format defined below  
any key followed by a ? means it is optional  

```
//What is in the json file
{"top": [<namespaceName>, <moduleName>],
"namespaces":{<namespaceName>:Namespace, ...}
}

//Definitions

Namespace={
  "namedtypes"? : NamedType[]
  "namedtypegens"? :NamedTypeGen[]
  "modules"? :{<modulename>:Module,...},
  "generators"? :{<genname>:Generator, ...}
}

Type = "BitIn" | "Bit" | ["Array", <N>, Type] | ["Record", [<key>, Type][]] | ["Named",NamedRef, Args?]

NamedRef = [<namespaceName>, <typeName>]
NamedType = {"name":<name>, "flippedname":<name>,"rawtype":Type}
NamedTypeGen={"name":<name>, "flippedname"?:<name>,"genparams":Parameter}

Module = {"type":Type, "configparams"?:Parameter, "defaultconfigargs"?:Args "metadata"?:Metadata, "def"?:ModuleDef}

ModuleDef = {"metadata"?:Metadata,
"instances"?: {<instname>:Instance,...}
"connections"?: Connection[]}

Generator = {"configparams"?:Parameters, "defaultconfigargs"?:Args, "genparams":Parameters, "defaultgenargs"?:Args, "typegen":NamedRef, "metadata"?:Metadata}

Instance = {"moduleref"?:InstantiatableReference, "generatorref"?:InstantiableReference, "genargs"?:Args, "configargs"?:Args, "metadata"?:Metadata}

InstantiatableReference = ["namespacename","InstantiatableName"]

Connection = [Wireable, Wireable, Metadata?]

//Will change to 
//Wireable = [<instname1.a.b>,<instname2.c.d>]
Wireable = [<instname>,<a>,<b>,...]
     //accesses instname.a.b If "instname" is "self" then this is the module's interface.
     //Note: a,b can be digits representing an index. 

Parameters = {<key>:ParameterType,...}
ParameterType = "Bool" | "Uint" | "Int" | "String" | "Type" | //NYI "Instantiatable"

Args = {<key>:ArgsValue}
ArgsValue = <Bool> | <Number> | <string> | Type | //NYI InstantiatableReference

Metadata={<key>:MetadataValue,...}
MetadataValue = <String> | <Number> (becomes double) | //NYI other structures
```
