local M = require "magmair"
local Mtypes = require "magmairtypes"
local Mstd = {}

local function constantInt(t)
  local ty = Mtypes.int(t.precision)
  return M.defineModule("constantInt_"..tostring(t.precision).."_"..tostring(t.value),ty)
end

local function reg(t)
  err(Mtypes.isType(t.type),"reg: type must be type")
  local delayport = Mtypes.record{{"input",t.type:input()},{"output",t.type:output()}}
  local ty = Mtypes.record{ {"get",t.type:output()},{"set",t.type:input()}}
  local mod = M.defineModule("reg_"..tostring(t.type), ty)
  return mod
end

local function assertModule(t)

end

-- There should be no IF statements in these generators!
Mstd.constantInt = M.declareModule{name="constantInt", parameters={"precision","value"},generator=constantInt}
--Mstd.constantUint = M.declareModule{name="constantUint", parameters={"precision","value"},generator=cUint}
--Mstd.constantBool = M.declareModule{name="constantBool", parameters={"value"}, generator=cBool}
--Mstd.bitCastUintInt = M.declareModule{name="bitcastUintInt",parameters={"prec"}}
--Mstd.bitCastIntUint = M.declareModule{name="bitcastIntUint",parameters={"prec"}}
--Mstd.muxBits = M.declareModule{name="mux",parameters={"width"}} -- bool?bits[W]:bits[W]

--Mstd.negInt = M.declareModule{name="neg", parameters={"prec"}} -- type:int
--Mstd.eqBits = M.declareModule{name="eq", parameters={"width"}} -- bits[W] == bits[W]
--Mstd.absInt = M.declareModule{name="abs", parameters={"prec"}} -- type:int

--Mstd.notBool = M.declareModule{name="boolNot"}
--Mstd.andBool = M.declareModule{name="boolAnd"}
--Mstd.orBool = M.declareModule{name="boolOr"}
--Mstd.xorBool = M.declareModule{name="boolXor"}

Mstd.reg = M.declareModule{name="reg", parameters={"type", "hasCE", "hasValid"}, generator=reg }
Mstd.assert = M.declareModule{name="assert", parameters={"error", "exit", "hasCE"}, generator=assertModule }

return Mstd