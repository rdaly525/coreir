
Type = [Vtype,Args]

VType = "Bit" 
      | "BitIn"
      | ["Array", VType, VInt]
      | ["Record", {<label>:[VType,VBool], ...}]
      | ["Arg",<key>]
      | ["Sel", VBool, VType, VType]

VInt = ["const", <value>]
     | ["Arg", <key>]
     | [binop, VInt,VInt]
     | ["Sel", VBool, VInt, VInt]

VBool = ["const", <value>]
      | ["Arg", <key>]
      | ["EqBool",VBool,VBool]
      | ["EqInt",VInt,VInt]
      | ["EqType",VType,VType]
      | ["Sel", VBool, VBool, VBool]

//Binary Type example
["Record", {
  "in":
    [
      ["Sel",
        ["EqInt",["const",1],["Arg","width"]],
        "Bit",
        ["Array","Bit",["Arg","width"]]
      ]
      ["const",True]
    ]
  "out":
    [
      ["Sel",
        ["EqInt",["const",1],["Arg","width"]],
        "Bit",
        ["Array","Bit",["Arg","width"]]
      ]
      ["const",True]
    ]
  }
]

          


