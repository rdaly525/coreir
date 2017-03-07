```
{"top": ModuleDef,
"namespaces":{"namespaceName":Namespace, ...}
}

Namespace={
  "types": {"typename":Type,...},
  "typeGeneratorDeclarations": {"typegenname":TypeGenDecl,...},
  "modules":{"modulename":Module,...},
  "generatorDeclarations":{"genname":GeneratorDeclaration, ...}
}

Type = "BitIn" | "BitOut" | ["Array",Type,N] | ["Record",{key:Type...} ] | [NamedTypeReference, GenArgs] | NamedTypeReference

NamedTypeReference=["namespaceName","typeName"]

TypeGenDecl={"genParameter":GenParameter}

//Module={"declaration":ModuleDecl, "definition":ModuleDef}

Module = {"type":Type,"config":GenParameter, "metadata":Metadata}

ModuleDef = {"metadata":Metadata,
"implementations":Metadata,
"instances": Instance[],
"connections": Connection[]}

Instance = {"module":InstantiatableReference, "args":GenArgs, "metadata":Metadata}

InstantiatableReference = ["namespacename","InstantiatableName"]
    "Instantiatable" means either a module or generator

Connection = [WireReference, WireReference, Metadata]

WireReference = ["instancename","a","b",...]
     accesses instancename.a.b. If "instancename" is "self" then this is the module's interface.

GeneratorDeclaration={"genParameter":GenParameter,"metadata":Metadata}

GenParameter={key:GenParameterType,...}
GenParameterType = "String" | "Uint" | "Int" | "Instantiatable"

GenArgs = {key:GenArgsValue}
GenArgsValue = String|Number|InstantiatableReference

Metadata={"key":MetadataValue,...}
MetadataValue = String | Number (becomes double)
```
