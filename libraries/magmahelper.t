local M = require "magmair.t"
local Mhelper = {}

------------ convenience
Mstd.cast = M.declaration{name="cast",parameters={"inputType","outputType"}}

-- purely wiring
--Mstd.record = M.declaration{name="tuple",parameters={"type"}} -- form record
Mstd.wire = M.declaration{name="wire",parameters={"type"}} -- implements tuplePacking, etc
Mstd.bitSlice = M.declaration{name="bitslice", parameters={"start","len","type"}}
Mstd.arraySlice = M.declaration{name="arrayslice", parameters={"type","start","len"})
Mstd.tupleSlice = M.declaration{name="tupleslice", parameters={"type","start","len"})

Mstd.neq = M.declaration{name="neq", parameters={"type"}}

Mstd.mux = M.declaration{name="mux",parameters={"type"}}
Mstd.constant = M.declaration{name="constant", parameters={"type","value"}}
Mstd.bitCast = M.declaration{name="cast",parameters={"inputType","outputType"}}

Mstd.add = M.declaration{name="add", parameters={"ltype","rtype","otype"}}
Mstd.mult = M.declaration{name="mult", parameters={"ltype","rtype","otype"}}
Mstd.lt = M.declaration{name="lt", parameters={"ltype","rtype"}}
Mstd.lte = M.declaration{name="lte", parameters={"ltype","rtype"}}
Mstd.gt = M.declaration{name="gt", parameters={"ltype","rtype"}}
Mstd.gte = M.declaration{name="gte", parameters={"ltype","rtype"}}

Mhelper.callArbitrate = M.declaration{name="callArbitrate",parameters={"type","N"}}