###How to read this:
Anything in <> should be filled in by user
Anything not in quotes is a json format defined below

```
//What is in the json file
{"top": [<namespaceName>, <moduleName>],
"namespaces":{<namespaceName>:Namespace, ...}
}

//Definitions

Namespace={
  "namedtypes": NamedType[]
  "namedtypegenerators":NamedTypeGenerators[]
  "modules":{<modulename>:Module,...},
  "generators":{<genname>:Generator, ...}
}

Type = ["BitIn"] | ["BitOut"] | ["Array", <N>, Type] | ["Record", [<key>, Type][]}] | ["NamedType", NamedTypeReference, Args]
TypeArgs = null | [<N>,Type] |  | 

NamedTypeReference=[<namespaceName>,<typeName>]
NamedType = {"typename":<name>, "flippedtypename":<name>,"type":Type}
NamedTypeGenerators={"typename":<name>, "flippedtypename":<name>,"genParameter":Parameter}

Module = {"type":Type,"configparams":Parameter, "metadata":Metadata,"def":ModuleDef}

ModuleDef = null | {"metadata":Metadata,
"implementations":Metadata,
"instances": {<instname>:Instance,...}
"connections": Connection[]}

Generator = {"configparameters":Parameters,"genparameters":Parameters, "typegen":NamedTypeReference, "metadata":Metadata}

Instance = {"instref":InstantiatableReference, "args":Args, "config":Args, "metadata":Metadata}

InstantiatableReference = ["namespacename","InstantiatableName"]

Connection = [Wireable, Wireable, Metadata]

Wireable = {"metadata":Metadata, "path":[<topname>,[<a>,<b>,...]]}
     accesses topname.a.b. If "topname" is "self" then this is the module's interface.

Parameters = null | {<key>:ParameterType,...}
ParameterType = "String" | "Uint" | "Int" | "Type" | "Instantiatable"

Args = null | {<key>:ArgsValue}
ArgsValue = <String> | <Number> | Type | InstantiatableReference

Metadata={<key>:MetadataValue,...}
MetadataValue = <String> | <Number> (becomes double)
```
