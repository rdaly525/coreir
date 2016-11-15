local Mtypes = {}

local MTypeFunctions = {}
local MTypeMT = {__index=MTypeFunctions, __tostring=function(ty)
                   local const = sel(ty.__constant,"_const","")
                   local inp = sel(ty.__input,"in_","")

  if ty.kind=="bool" then
    return inp.."bool"..const
  elseif ty.kind=="null" then
    return "null"
  elseif ty.kind=="int" then
    return inp.."int"..ty.precision..const
  elseif ty.kind=="uint" then
    return inp.."uint"..ty.precision..const
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

Mtypes._bool={[true]={},[false]={}}
function Mtypes.bool(input,const) 
  input = (input==true); const = (const==true);
  if Mtypes._bool[input][const]==nil then Mtypes._bool[input][const] = setmetatable({kind="bool",__input=input,__constant=const}, MTypeMT) end
  return Mtypes._bool[input][const]
end

Mtypes._uint={}
function Mtypes.uint(prec,input,const)
  err(prec==math.floor(prec), "uint precision should be integer, but is "..tostring(prec) )
  input = (input==true); const = (const==true);
  Mtypes._uint[input] = Mtypes._uint[input] or {}
  Mtypes._uint[input][const] = Mtypes._uint[input][const] or {}
  Mtypes._uint[input][const][prec] = Mtypes._uint[input][const][prec] or setmetatable({kind="uint",precision=prec,__input=input,__constant=const},MTypeMT)
  return Mtypes._uint[input][const][prec]
end

Mtypes._int={}
function Mtypes.int(prec,input,const)
  err(prec==math.floor(prec), "int precision should be integer, but is "..tostring(prec) )
  input = (input==true); const = (const==true);
  Mtypes._int[input] = Mtypes._int[input] or {}
  Mtypes._int[input][const] = Mtypes._int[input][const] or {}
  Mtypes._int[input][const][prec] = Mtypes._int[input][const][prec] or setmetatable({kind="int",precision=prec,__input=input,__constant=const},MTypeMT)
  return Mtypes._int[input][const][prec]
end


Mtypes._array={}

function Mtypes.array( _type, N )
  err( Mtypes.isType(_type), "first index to array2d must be type" )
  assert( type(N)=="number" )

  err(N==math.floor(N), "non integer array width "..tostring(N))

  -- dedup the arrays
  local ty = setmetatable( {kind="array", over=_type, size=N}, TypeMT )
  return deepsetweak(Mtypes._array, {_type,N}, ty)
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
    return Mtypes.bool( inp, self.__constant )
  elseif self.kind=="int" then
    return Mtypes.int( self.precision, inp, self.__constant )
  elseif self.kind=="uint" then
    return Mtypes.uint( self.precision, inp, self.__constant )
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
function MTypeFunctions:isArray() return self.kind=="array" end


-- a tuple is a record with contiguous keys from 0...N
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

function MTypeFunctions:slice(startIdx,len)
  err(type(startIdx)=="number", "Type:slice() start index must be number")
  err(type(len)=="number", "Type:slice() length must be number")

  if self.kind=="record" then
    local newlist = {}
    err(self:isTuple(), ":slice() record type must be tuple")

    for i=startIdx,startIdx+len-1 do
      table.insert( newlist, {i-startIdx,self:index(i)} )
    end
    return Mtypes.record(newlist)
  else
    err(false,":index() only works on records and arrays")
  end
end

-- is this type or any subcomponents of it an input?
function MTypeFunctions:anyInputs()
  if self.kind=="bool" or self.kind=="int" or self.kind=="uint" then
    return self.__input
  elseif self.kind=="record" then
    local res = false
    for _,v in pairs(self.list) do res = res or v[2]:anyInputs() end
    return res
  end
  assert(false)
end

-- returns the entries of an aggregate in form { {key1,type1}, {key2, type2} }
function MTypeFunctions:getKeyList()
  if self.kind=="record" then
    return self.list
  end
  assert(false)
end

function MTypeFunctions:flip()
  if self.kind=="bool" then
    return Mtypes.bool( not self.__input, self.__constant )
  elseif self.kind=="int" then
    return Mtypes.int( self.precision, not self.__input, self.__constant )
  elseif self.kind=="uint" then
    return Mtypes.uint( self.precision, not self.__input, self.__constant )
  elseif self.kind=="record" then
    local l = {}
    for k,v in ipairs(self.list) do
      table.insert(l, {v[1],v[2]:flip()})
    end
    return Mtypes.record(l)
  end
  assert(false)

end

return Mtypes