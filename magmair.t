Mtypes = require "magmairtypes"
M = {}

local nameCnt = 0
local function generateName()
  nameCnt = nameCnt + 1
  return "w"..nameCnt
end

local ValueMT
local ValueFunctions = {}

-- given a selector, we want to be able to query a few things:
-- __dbg: Can it be wired? If one of its children is an input and has already been wired, we can't (this could either be wired upstream or downstream)
-- __wires: what are its wires?
-- __terminal: is it terminal? ie are any of its children also wired? (nil means unwired, true means terminal, false means nonterminal)
-- __selectors: we want to be able to select subcomponents of it
-- __instance: What instance is it a selector of? 
-- __input: What is its parent? either another selector, or an instance
local function genSelect(tab, idx, value)
  if ValueFunctions[idx]~=nil then return ValueFunctions[idx] end

  err(value==nil, "Can not assign to selector!")
  err(type(idx)=="string" or type(idx)=="number", "idx is not a string or number")

  err(tab.__type:isRecord() or tab.__type:isArray(), "attempting to select index '"..idx.."' of ("..tab.__name.."), which is not an array or record!")

  local res = {__kind="select",__input=tab,__idx=idx,__name=tab.__name.."."..tostring(idx), __selectors={}, __instance=tab.__instance, __wires={}, __dbg=""}
  res.__type = tab.__type:index(idx)

  setmetatable(res,ValueMT)
  rawset(tab,idx,res)

  return res
end

ValueMT = { __index = genSelect, __newindex = genSelect }

function ValueFunctions:invalidate(dbg)
  assert(type(dbg)=="string")

  self.__dbg = dbg

  if self.__kind=="select" then
    self.__input:invalidate(dbg)
  end
end

function ValueFunctions:wire( other, __skipBidirection )
  err(M.isValue(other),"wire target is not a wire value")

  err( #self.__dbg==0, "Error wiring ("..self.__name..") to ("..other.__name.."), the requested value ("..self.__name..") has already been wired! at loc "..self.__dbg.."END")

  err( self.__type==other.__type:flip(), "Error, wiring types don't match! Wiring "..self.__name.." with type "..tostring(self.__type).." to "..other.__name.." with type "..tostring(other.__type))

  table.insert(self.__wires, other)

  -- At this point a few things need to happen:
  -- 1) if subfields of this value have any inputs, we need to invalidate all parents to prevent multiple drivers
  -- 2) We need to invalide all children that are inputs

  if self.__type:anyInputs() then
    self:invalidate(debug.traceback())
  end

  if self.__type:isArray() or self.__type:isRecord() then
    for k,v in pairs(self.__type:getKeyList()) do
      local sel = self[v[1]]

      if sel.__type:anyInputs() then
        sel.__dbg = self.__dbg
      end
    end
  end

  if __skipBidirection~=true then other:wire(self,true) end
end

-- Note that type should be the type of the _external_ interface.
-- i.e. inputs (to the module) should be marked as inputs
function M.parameter( type )
  err(Mtypes.isType(type), "type must be type")
  local tab = {__kind="parameter", __type=type:flip(), __name=generateName(),__dbg="",__wires={}}
  tab.__instance = tab
  return setmetatable(tab,ValueMT)
end

function M.isValue(w)
  return getmetatable(w)==ValueMT
end

DefinitionFunctions = {}
DefinitionMT={__index=DefinitionFunctions}
function M.defineModule( name, ty )
  err(type(name)=="string","name is not a string")
  err(Mtypes.isType(ty),"type is not a magma type")
  return setmetatable({name=name, parameter=M.parameter(ty), type = ty, instances = {}, namesToInstances={}}, DefinitionMT)
end

function M.isDefinition(f) return getmetatable(f)==DefinitionMT end

function DefinitionFunctions:addInstance( module, name )
  err(M.isDefinition(module), "module must be module definition")
  err(type(name)=="string", "instance name must be string")
  err( self.namesToInstances[name]==nil, "Error, name '"..name.."' is already used" )
  local tab = { __kind="instance", __module=module, __name=name, __wiredebug={} }
  tab.__instance = tab
  tab.__type = module.type
  tab.__dbg = "" 
  tab.__wires = {}
  local res = setmetatable(tab,ValueMT)
  table.insert( self.instances, res )
  self.namesToInstances[name] = res
  return res
end

function DefinitionFunctions:pickle()
  local t = {name = self.name, instructions={}}
  table.insert(t.instructions,{"parameter",self.parameter.__name,tostring(self.parameter.__type)})

  local seenWires = {}
  local seenInstances = {}
  local Q = {}

  local function addWire(a,b)
    assert(type(a)=="string")
    assert(type(b)=="string")

    if seenWires[a]==nil and seenWires[a][b]==nil then
      table.insert( t.instructions, {"wire", a, b} )
      seenWires[a] = seenWires[a] or {}
      seenWires[b] = seenWires[b] or {}
      seenWires[a][b] = 1
      seenWires[b][a] = 1
    end
  end

  local function collectWires( connectionTable, selector, selectorTable )
    assert(type(selector)=="string") -- reference to the selector

    if M.isValue(connectionTable) then
      -- this is a connection to something! this is a wire instruction
      addWire(selector.name,connectionTable.name)
      assert(M.isValue(connectionTable))
      assert(connectionTable.__instance.kind=="instance")
      seenInstances[connectionTable.__instance] = 1
    else
      -- this is a table of selectors/wires
      for k,v in pairs(connectionTable) do
        table.insert( t.instructions, {"select", selectorTable[k].__name, selector, selectorTable[k].__idx } )
        collectWires(v,selectorTable[k], selectorTable[k].__selectors)
      end
    end
  end

  while #Q>0 do
    local next = table.remove(Q,1)
    table.insert( t.instructions, {"instantiate", next.__name, next.__module.name} )
    seenInstances[next] = 1
    collectWires( next.wires, next, next.selectors )
  end

  return t
end

DeclarationFunctions = {}

function declCall(t,args)
  local mod = t.generator(args)
  err(M.isDefinition(mod), "output of generator must be module definition")
  return mod
end

DeclarationMT={__index=DeclarationFunctions,__call=declCall}
function M.declareModule(tab)
  err(type(tab)=="table", "declareModule input must be table")
  err(type(tab.name)=="string", "name must be string")
  err(type(tab.parameters)=="table" or tab.parameters==nil, "parameters must be table or nil")
  err(type(tab.generator)=="function", "generator must be function")
  return setmetatable(tab,DeclarationMT)
end

return M
