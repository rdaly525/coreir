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
  "namedtypegenerators"? :NamedTypeGenerator[]
  "modules"? :{<modulename>:Module,...},
  "generators"? :{<genname>:Generator, ...}
}

Type = "BitIn" | "BitOut" | ["Array", <N>, Type] | ["Record", [<key>, Type][]}] | ["Named", NamedReference, Args]

NamedReference=[<namespaceName>,<typeName>]
NamedType = {"typename":<name>, "flippedtypename":<name>,"type":Type}
NamedTypeGenerator={"typename":<name>, "flippedtypename":<name>,"genParameter":Parameter}

Module = {"type":Type, "configparams"?:Parameter, "metadata"?:Metadata, "def"?:ModuleDef}

ModuleDef = {"metadata"?:Metadata,
"implementations"?:Metadata,
"instances"?: {<instname>:Instance,...}
"connections"?: Connection[]}

Generator = {"configparameters"?:Parameters,"genparameters":Parameters, "typegen":NamedTypeReference, "metadata"?:Metadata}

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
