local Mtypes = {}

local MTypeFunctions = {}
local MTypeMT = {__index=MTypeFunctions, __tostring=function(ty)
            local const = sel(ty.constant,"_const","")
  if ty.kind=="bool" then
    return "bool"..const
  elseif ty.kind=="null" then
    return "null"
  elseif ty.kind=="int" then
    return "int"..ty.precision..const
  elseif ty.kind=="uint" then
    return "uint"..ty.precision..const
  elseif ty.kind=="bits" then
    return "bits"..ty.precision..const
  elseif ty.kind=="float" then
    return "float"..ty.precision..const
  elseif ty.kind=="array" then
    return tostring(ty.over).."["..table.concat(ty.size,",").."]"
  elseif ty.kind=="record" then
    if ty:isTuple() then
      return "{"..table.concat(map(ty.list, function(n) return tostring(n[2]) end), ",").."}"
    else
      return "{"..table.concat(map(ty.list, function(n) return tostring(n[1]).."="..tostring(n[2]) end), ",").."}"
    end
  end

  print("Error, typeToString input doesn't appear to be a type, ",ty.kind)
  assert(false)
end}

function Mtypes.isType(t)
  return getmetatable(t)==MTypeMT
end

-- {const,input}
local _flags = {}
function Mtypes.flags(t)
  if t==nil then t={} end
  local const = t.const
  if const==nil then const=false end
  local inp = t.input
  if inp==nil then inp=false end
  _flags[const]  = _flags[const] or {}
  _flags[const][inp]  = _flags[const][inp] or {input=inp,const=const}
  return _flags[const][inp]
end

Mtypes._bool={}
function Mtypes.bool(flags) 
  flags = Mtypes.flags(flags)
  if Mtypes._bool[flags]==nil then Mtypes._bool[flags] = setmetatable({kind="bool",flags=flags}, MTypeMT) end
  return Mtypes._bool[flags]
end

Mtypes._uint={}
function Mtypes.uint(prec,flags)
  flags = Mtypes.flags(flags)
  err(prec==math.floor(prec), "uint precision should be integer, but is "..tostring(prec) )
  Mtypes._uint[flags] = Mtypes._uint[flags] or {}
  Mtypes._uint[flags][prec] = Mtypes._uint[flags][prec] or setmetatable({kind="uint",precision=prec,flags=flags},MTypeMT)
  return Mtypes._uint[flags][prec]
end

Mtypes._int={}
function Mtypes.int(prec,flags)
  flags = Mtypes.flags(flags)
  assert(prec==math.floor(prec))
  Mtypes._uint[flags] = Mtypes._uint[flags] or {}
  Mtypes._int[flags][prec] = Mtypes._int[flags][prec] or setmetatable({kind="int",precision=prec,flags=flags},MTypeMT)
  return Mtypes._int[flags][prec]
end


Mtypes._array={}

function Mtypes.array2d( _type, w, h )
  err( Mtypes.isType(_type), "first index to array2d must be type" )
  assert( type(w)=="number" )
  err( type(h)=="number" or h==nil, "array2d h must be nil or number, but is:"..type(h))
  if h==nil then h=1 end -- by convention, 1d arrays are 2d arrays with height=1
  err(w==math.floor(w), "non integer array width "..tostring(w))
  assert(h==math.floor(h))

  -- dedup the arrays
  local ty = setmetatable( {kind="array", over=_type, size={w,h}}, TypeMT )
  return deepsetweak(Mtypes._array, {_type,w,h}, ty)
end

Mtypes._records = {}

-- list should be key,type pairs: {{key1,type1},{key2,type2}}
function Mtypes.record( list )
  assert(type(list)=="table")
  assert(keycount(list)==#list)
  err(#list>0, "no empty record types!")

  local flatlist={}
  for _,v in pairs(list) do 
    err( type(v[1])=="string" or type(v[1])=="number", "record key should be string or number not "..type(v[1]))
    err( Mtypes.isType(v[2]), "record type must be Magma type")
    table.insert(flatlist,v[1])
    table.insert(flatlist,v[2])
  end

  -- we want to allow a tuple with one item to be a real type, for the same reason we want there to be an array of size 1.
  -- This means we can parameterize a design from tuples with 1->N items and it will work the same way.

  Mtypes._records[#flatlist] = Mtypes._records[#flatlist] or {}
  local tup = setmetatable( {kind="record", list = list }, MTypeMT )
  local res = deepsetweak( Mtypes._records[#flatlist], flatlist, tup )
  assert(Mtypes.isType(res))
  assert(#res.list==#list)
  return res
end

function MTypeFunctions:setInput(inp)
  if self.kind=="bool" then
    if self.flags.input==inp then return self
    else return Mtypes.bool(Mtypes.flags{const=self.flags.const,input=inp}) end
  elseif self.kind=="int" then
    if self.flags.input==inp then return self
    else return Mtypes.int( self.precision, Mtypes.flags{const=self.flags.const,input=inp}) end
  elseif self.kind=="uint" then
    if self.flags.input==inp then return self
    else return Mtypes.uint( self.precision, Mtypes.flags{const=self.flags.const,input=inp}) end
  elseif self.kind=="record" then
    local l = {}
    for k,v in ipairs(self.list) do
      table.insert(l, {v[1],v[2]:setInput(inp)})
    end
    return Mtypes.record(l)
  end
  assert(false)
end


function MTypeFunctions:input() return self:setInput(true) end
function MTypeFunctions:output() return self:setInput(false) end

function MTypeFunctions:isFloat() return self.kind=="float" end
function MTypeFunctions:isBool() return self.kind=="bool" end
function MTypeFunctions:isInt() return self.kind=="int" end
function MTypeFunctions:isUint() return self.kind=="uint" end
function MTypeFunctions:isRecord() return self.kind=="record" end

function MTypeFunctions:isTuple()
  if self.kind~="record" then return false end
  local low,high
  for k,v in pairs(self.list) do
    if type(v[1])~="number" then return false end
    if low==nil or v[1]<low then low=v[1] end
    if high==nil or v[1]>high then high=v[1] end
  end
  return low==0 and (high-low+1 == #self.list)
end

function MTypeFunctions:index(idx)
  if self.kind=="record" then
    for _,v in pairs(self.list) do
      if v[1]==idx then return v[2] end
    end
    err(false,":index(), '"..tostring(idx).."' not found on type "..tostring(self))
  else
    err(false,":index() only works on records and arrays")
  end
end


return Mtypes