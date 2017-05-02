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

Module = {"type":Type, "configparams"?:Parameter, "metadata"?:Metadata, "def"?:ModuleDef}

ModuleDef = {"metadata"?:Metadata,
"implementations"?:Metadata,
"instances"?: {<instname>:Instance,...}
"connections"?: Connection[]}

Generator = {"configparams"?:Parameters,"genparams":Parameters, "typegen":NamedRef, "metadata"?:Metadata}

Instance = {"instref":InstantiatableReference, "genargs"?:Args, "config"?:Args, "metadata"?:Metadata}

InstantiatableReference = ["namespacename","InstantiatableName"]

Connection = [Wireable, Wireable, Metadata?]

Wireable = [<topname>,<a>,<b>,...]
     accesses topname.a.b. If "topname" is "self" then this is the module's interface.

Parameters = {<key>:ParameterType,...}
ParameterType = "String" | "Int" | "Type" | //NYI "Uint" | "Instantiatable"

Args = {<key>:ArgsValue}
ArgsValue = <String> | <Number> | Type | //NYI InstantiatableReference

Metadata={<key>:MetadataValue,...}
MetadataValue = <String> | <Number> (becomes double)
```
