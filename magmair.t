Mtypes = require "magmairtypes"
M = {}

local nameCnt = 0
local function generateName()
  nameCnt = nameCnt + 1
  return "w"..nameCnt
end

local ValueFunctions = {}
local ValueMT = { __index=ValueFunctions }

function ValueFunctions:select( idx, name )
  err(type(idx)=="string" or type(idx)=="number", "idx is not a string or number")
  err(type(name)=="string" or name==nil,"name is not a string")
  if name==nil then name=generateName() end
  err(self.__type:isRecord() or self.__type:isArray(), "selecting into something other than an array or record!")
  local tab = {__kind="select",__input=self,__idx=idx,__name=name, __selectors={}, __instance=self.__instance}
  tab.__type = self.__type:index(idx)
  return setmetatable(tab,ValueMT)
end


-- return a path through the connections table to get to this value
-- index 1 is always 'wires' (the name of the connection table
function ValueFunctions:trace()
  if self.kind=="instance" or self.kind=="parameter" then
    return {"__wires"}
  elseif self.kind=="select" then
    local t = self.input:trace()
    table.insert(t,self.__idx)
    return t
  end
end

function ValueFunctions:wire( other, name )
  err(M.isValue(b),"b is not a wire value")
  err(type(name)=="string" or name==nil,"name is not a string")
  local trce = self:trace()
  local connectionTable = self.__instance
  for i=1,#trce-1 do
    connectionTable[trce[i]] = connectionTable[trce[i]] or {}
    connectionTable = connectionTable[trce[i]]
  end
  err( connectionTable[trce[#trce]]==nil, "Error, a subset of the requested connection have already been wired!")
  connectionTable[trce[#trce]] = other
  other:wire(self,name)
end

function M.parameter( type )
  err(Mtypes.isType(type), "type must be type")
  local tab = {__kind="parameter", __type=type, __name=generateName()}
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
  return setmetatable({name=name, parameter=M.parameter(ty)}, DefinitionMT)
end

function M.isDefinition(f) return getmetatable(f)==DefinitionMT end

function DefinitionFunctions:addInstance( module, name )
  err(M.isModuleDefinition(module), "module must be module definition")
  err(type(name)=="string", "instance name must be string")
  local tab = { __kind="instance", __module=module, __name=name }
  tab.__instance = tab
  return setmetatable(tab,ValueMT)
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