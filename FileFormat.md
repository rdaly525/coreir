```
{"top": [namespaceName, ModuleName],
"namespaces":{"namespaceName":Namespace, ...}
}

Namespace={
  "types": {"typename":Type,...},
  "typeGeneratorDeclarations": {"typegenname":TypeGenDecl,...},
  "modules":{"modulename":Module,...},
  "generators":{"genname":Generator, ...}
}

Type = {"type": Type}
TypeKind = BitIn | BitOut | Array | Record | NamedType
TypeArgs = 
Type = "BitIn" | "BitOut" | ["Array":[N,Type]] | ["Record",{key:Type...} ] | [NamedTypeReference, GenArgs] | NamedTypeReference

NamedTypeReference=["namespaceName","typeName"]

TypeGenDecl={"genParameter":GenParameter}

Module = {"type":Type,"config":GenParameter, "metadata":Metadata,"def":ModuleDef}

ModuleDef = None | {"metadata":Metadata,
"implementations":Metadata,
"instances": Instance[],
"connections": Connection[]}

Generator = {"genParameter":GenParameter, "typegen":NamedTypeReference, "metadata":Metadata}

Instance = {"instancename": name, "instref":InstantiatableReference, "args":GenArgs, "config":GenArgs, "metadata":Metadata}

InstantiatableReference = ["namespacename","InstantiatableName"]

Connection = [WireReference, WireReference, Metadata]

WireReference = ["instancename","a","b",...]
     accesses instancename.a.b. If "instancename" is "self" then this is the module's interface.

GenParameter= None | {key:GenParameterType,...}
GenParameterType = "String" | "Uint" | "Int" | "Type" | "Instantiatable"

GenArgs = None | {key:GenArgsValue}
GenArgsValue = String | Number | Type | InstantiatableReference

Metadata={"key":MetadataValue,...}
MetadataValue = String | Number (becomes double)
```
