###How to read this:  
Anything in <> should be filled in by user as a string  
Anything not in quotes is a json format defined below  
any key followed by a ? means it is optional  

```
//What is in the json file
{
  "top: NamedRef,
  namespaces: {<namespaceName>:Namespace, ...}
}


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
     | ["Record", [[<key>,Type],... ] 
     | ["Named",NamedRef, Args?]

//This could be referring a type, module, or generator
NamedRef = "<namespaceName>.<name>"

NamedType = {"flippedname":<name>,"rawtype":Type}
NamedTypeGen = {"flippedname"?:<name>,"genparams":Parameter}

//Note if there are no instances and no connections, this is a declaration
Module = {
  "type":Type,
  "modparams"?:Parameter,
  "defaultmodargs"?:Values,
  "genref"?:NamedRef, //Used for generated modules
  "genargs"?:Values, //'' '' 
  "instances"?:{<instname>:Instance,...},
  "connections"?: Connection[]
}

Generator = {
  "typegen":NamedRef
  "genparams":Parameters,
  "defaultgenargs"?:Consts,

}

Instance = {
  "genref"?:NamedRef,
  "genargs"?:Values,
  "modref"?:NamedRef,
  "modargs"?:Values
}

Connection = [Wireable, Wireable]

//accesses instname.a.b If "instname" is "self" then this is the module's interface.
//Note: a,b can be digits representing an index. 
Wireable = "<instname>,<a>,<b>,..."


//The following is my Value IR. 
//This contains a small IR representing constants and Referneces to generator/module args. This will be expanded

ValueType = "Bool"
          | "Int"
          | ["BitVector" <N>]
          | "String"
          | "CoreIRType"

Params = {<field>:ValueType,...}

Arg = [ValueType, "Arg", <field>]
Const = [ValueType, <Val>]

Value = Arg
      | Const

Values = {<field>:Value,...}

```
