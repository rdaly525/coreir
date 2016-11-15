local M = require "magmair"
local Mtypes = require "magmairtypes"
local Mhelper = {}

function tupleSlice(t)
  err(Mtypes.isType(t.type),"tupleSlice: type must be type")
  err( t.type:isTuple(), "tupleSlice: type must be tuple")
  err( type(t.start)=="number", "tupleSlice: start must be number")
  err( type(t.len)=="number", "tupleSlice: len must be number")
  local ty = Mtypes.record{ {"input",t.type:input()}, {"output",t.type:slice(t.start,t.len):output()} }
  return M.defineModule("tupleSlice_"..tostring(t.type).."_start_"..tostring(t.start).."_"..tostring(t.len), ty)
end

function cast(t)
  err(Mtypes.isType(t.inputType),"cast: inputType must be type")
  err(Mtypes.isType(t.outputType),"cast: outputType must be type")
  local ty = Mtypes.record{ {"input",t.inputType:input()}, {"output",t.outputType:output()} }
  return M.defineModule("cast_"..tostring(t.inputType).."_to_"..tostring(t.outputType), ty)
end

function constant(t)
  err(Mtypes.isType(t.type),"constant: type must be type")
  return M.defineModule("constant_"..tostring(t.type)..tostring(t.value), t.type:output())
end

function binop(op)
  assert(type(op)=="string")
  return function(t)
    err(Mtypes.isType(t.lType),"binop: lType must be type")
    err(Mtypes.isType(t.rType),"binop: rType must be type")
    err(Mtypes.isType(t.outputType),"binop: outputType must be type")
    local tytup = Mtypes.record{ {0,t.lType:input()}, {1,t.rType:input()} }
    local ty = Mtypes.record{ {"input",tytup}, {"output",t.outputType:output()} }
    return M.defineModule(op.."_"..tostring(t.lType).."_"..tostring(t.rType).."_"..tostring(t.outputType), ty)
         end
end

function selectGen(t)
  err(Mtypes.isType(t.type),"select: type must be type")

  local tytup = Mtypes.record{ {0,Mtypes.bool():input()},{1,t.type:input()}, {2,t.type:input()} }
  local ty = Mtypes.record{ {"input",tytup}, {"output",t.type:output()} }
  return M.defineModule("select_"..tostring(t.type), ty)
end

------------ convenience
Mhelper.cast = M.declareModule{name="cast",parameters={"inputType","outputType"},generator=cast}

-- purely wiring
--Mhelper.record = M.declareModule{name="tuple",parameters={"type"}} -- form record
--Mhelper.wire = M.declareModule{name="wire",parameters={"type"}} -- implements tuplePacking, etc
--Mhelper.bitSlice = M.declareModule{name="bitslice", parameters={"start","len","type"}}
--Mhelper.arraySlice = M.declareModule{name="arrayslice", parameters={"type","start","len"}}
Mhelper.tupleSlice = M.declareModule{name="tupleslice", parameters={"type","start","len"}, generator = tupleSlice}

--Mhelper.neq = M.declareModule{name="neq", parameters={"type"}}

--Mhelper.mux = M.declareModule{name="mux",parameters={"type"}}
Mhelper.constant = M.declareModule{name="constant", parameters={"type","value"}, generator = constant}
--Mhelper.bitCast = M.declareModule{name="cast",parameters={"inputType","outputType"}}

Mhelper.add = M.declareModule{name="add", parameters={"lType","rType","outputType"}, generator = binop("add")}
--Mhelper.mult = M.declareModule{name="mult", parameters={"ltype","rtype","otype"}}
--Mhelper.lt = M.declareModule{name="lt", parameters={"ltype","rtype"}}
--Mhelper.lte = M.declareModule{name="lte", parameters={"ltype","rtype"}}
--Mhelper.gt = M.declareModule{name="gt", parameters={"ltype","rtype"}}
--Mhelper.gte = M.declareModule{name="gte", parameters={"ltype","rtype"}}

--Mhelper.callArbitrate = M.declareModule{name="callArbitrate",parameters={"type","N"}}

Mhelper.select = M.declareModule{name="select", parameters={"type"}, generator = selectGen}

return Mhelper