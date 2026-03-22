local M = {}

local unpack = unpack or table.unpack
local floor = math.floor
local huge = math.huge
local abs = math.abs
local max = math.max
local min = math.min
local byte = string.byte
local sub = string.sub
local concat = table.concat
local sort = table.sort
local getmetatable = getmetatable
local setmetatable = setmetatable
local type = type
local tostring = tostring
local select = select
local error = error
local pairs = pairs
local pcall = pcall

local LUA_SIGNATURE = "\27Lua"
local LUAC_VERSION = 0x54
local LUAC_FORMAT = 0
local LUAC_DATA = "\25\147\r\n\26\n"
local LUAC_INT = 0x5678
local LUAC_NUM = 370.5

local LUA_VNIL = 0
local LUA_VFALSE = 1
local LUA_VTRUE = 17
local LUA_VNUMINT = 3
local LUA_VNUMFLT = 19
local LUA_VSHRSTR = 4
local LUA_VLNGSTR = 20

local SIZE_OP = 7
local SIZE_A = 8
local SIZE_B = 8
local SIZE_C = 8
local SIZE_Bx = SIZE_B + SIZE_C + 1
local SIZE_Ax = SIZE_Bx + SIZE_A
local SIZE_sJ = SIZE_Ax

local POS_OP = 0
local POS_A = POS_OP + SIZE_OP
local POS_k = POS_A + SIZE_A
local POS_B = POS_k + 1
local POS_C = POS_B + SIZE_B
local POS_Bx = POS_k
local POS_Ax = POS_A
local POS_sJ = POS_A

local OFFSET_sBx = 65535
local OFFSET_sJ = 16777215
local OFFSET_sC = 127

local TM_EVENTS = {
  [6] = "__add",
  [7] = "__sub",
  [8] = "__mul",
  [9] = "__mod",
  [10] = "__pow",
  [11] = "__div",
  [12] = "__idiv",
  [13] = "__band",
  [14] = "__bor",
  [15] = "__bxor",
  [16] = "__shl",
  [17] = "__shr",
  [18] = "__unm",
  [19] = "__bnot",
  [20] = "__lt",
  [21] = "__le",
  [22] = "__concat",
  [23] = "__call",
  [24] = "__close",
}

local OPCODES = {
  [0] = "MOVE",
  "LOADI",
  "LOADF",
  "LOADK",
  "LOADKX",
  "LOADFALSE",
  "LFALSESKIP",
  "LOADTRUE",
  "LOADNIL",
  "GETUPVAL",
  "SETUPVAL",
  "GETTABUP",
  "GETTABLE",
  "GETI",
  "GETFIELD",
  "SETTABUP",
  "SETTABLE",
  "SETI",
  "SETFIELD",
  "NEWTABLE",
  "SELF",
  "ADDI",
  "ADDK",
  "SUBK",
  "MULK",
  "MODK",
  "POWK",
  "DIVK",
  "IDIVK",
  "BANDK",
  "BORK",
  "BXORK",
  "SHRI",
  "SHLI",
  "ADD",
  "SUB",
  "MUL",
  "MOD",
  "POW",
  "DIV",
  "IDIV",
  "BAND",
  "BOR",
  "BXOR",
  "SHL",
  "SHR",
  "MMBIN",
  "MMBINI",
  "MMBINK",
  "UNM",
  "BNOT",
  "NOT",
  "LEN",
  "CONCAT",
  "CLOSE",
  "TBC",
  "JMP",
  "EQ",
  "LT",
  "LE",
  "EQK",
  "EQI",
  "LTI",
  "LEI",
  "GTI",
  "GEI",
  "TEST",
  "TESTSET",
  "CALL",
  "TAILCALL",
  "RETURN",
  "RETURN0",
  "RETURN1",
  "FORLOOP",
  "FORPREP",
  "TFORPREP",
  "TFORCALL",
  "TFORLOOP",
  "SETLIST",
  "CLOSURE",
  "VARARG",
  "VARARGPREP",
  "EXTRAARG",
}

local function pack(...)
  return { n = select("#", ...), ... }
end

local function trim_results(results, wanted)
  local out = {}
  for i = 1, wanted do
    out[i] = results[i]
  end
  return out
end

local function is_false(value)
  return value == nil or value == false
end

local function mask(bits)
  return 2 ^ bits - 1
end

local function bit_and(a, b)
  local result = 0
  local bitval = 1
  a = a % 4294967296
  b = b % 4294967296
  while a > 0 or b > 0 do
    local aa = a % 2
    local bb = b % 2
    if aa == 1 and bb == 1 then
      result = result + bitval
    end
    a = floor(a / 2)
    b = floor(b / 2)
    bitval = bitval * 2
  end
  return result
end

local function bit_or(a, b)
  local result = 0
  local bitval = 1
  a = a % 4294967296
  b = b % 4294967296
  while a > 0 or b > 0 do
    local aa = a % 2
    local bb = b % 2
    if aa == 1 or bb == 1 then
      result = result + bitval
    end
    a = floor(a / 2)
    b = floor(b / 2)
    bitval = bitval * 2
  end
  return result
end

local function bit_xor(a, b)
  local result = 0
  local bitval = 1
  a = a % 4294967296
  b = b % 4294967296
  while a > 0 or b > 0 do
    local aa = a % 2
    local bb = b % 2
    if aa ~= bb then
      result = result + bitval
    end
    a = floor(a / 2)
    b = floor(b / 2)
    bitval = bitval * 2
  end
  return result
end

local function bit_not(a)
  return 4294967295 - (a % 4294967296)
end

local function shift_left(a, n)
  return (a * 2 ^ n) % 4294967296
end

local function shift_right(a, n)
  a = a % 4294967296
  return floor(a / 2 ^ n)
end

local function idiv(a, b)
  if b == 0 then
    error("attempt to divide by zero")
  end
  local q = a / b
  if q >= 0 then
    return floor(q)
  end
  local i = floor(q)
  if i == q then
    return i
  end
  return i - 1
end

local function bytes_to_uint_le(bytes)
  local value = 0
  for i = #bytes, 1, -1 do
    value = value * 256 + byte(bytes, i)
  end
  return value
end

local function uint_to_int(value, byte_count)
  local limit = 2 ^ (byte_count * 8)
  local sign = limit / 2
  if value >= sign then
    return value - limit
  end
  return value
end

local function decode_double_le(bytes)
  local b = {}
  for i = 1, 8 do
    b[i] = byte(bytes, i)
  end
  local mantissa = 0
  for i = 1, 6 do
    mantissa = mantissa + b[i] * 2 ^ ((i - 1) * 8)
  end
  mantissa = mantissa + (b[7] % 16) * 2 ^ 48
  local exponent = floor(b[8] % 128) * 16 + floor(b[7] / 16)
  local sign = b[8] >= 128 and -1 or 1
  if exponent == 0 then
    if mantissa == 0 then
      return sign == 1 and 0 or -0
    end
    return sign * 2 ^ (-1022) * (mantissa / 2 ^ 52)
  end
  if exponent == 2047 then
    if mantissa == 0 then
      return sign * huge
    end
    return 0 / 0
  end
  return sign * 2 ^ (exponent - 1023) * (1 + mantissa / 2 ^ 52)
end

local Reader = {}
Reader.__index = Reader

function Reader.new(data)
  return setmetatable({ data = data, pos = 1 }, Reader)
end

function Reader:read(n)
  local s = sub(self.data, self.pos, self.pos + n - 1)
  if #s ~= n then
    error("unexpected end of bytecode chunk")
  end
  self.pos = self.pos + n
  return s
end

function Reader:read_byte()
  local b = byte(self.data, self.pos)
  if not b then
    error("unexpected end of bytecode chunk")
  end
  self.pos = self.pos + 1
  return b
end

local function read_unsigned(reader, limit)
  local x = 0
  limit = floor(limit / 128)
  while true do
    local b = reader:read_byte()
    if x >= limit then
      error("integer overflow while reading bytecode")
    end
    x = x * 128 + (b % 128)
    if b >= 128 then
      return x
    end
  end
end

local function read_int(reader)
  return read_unsigned(reader, 2147483647)
end

local function read_size(reader)
  return read_unsigned(reader, 9007199254740991)
end

local function read_lua_integer(reader, size)
  return uint_to_int(bytes_to_uint_le(reader:read(size)), size)
end

local function read_lua_number(reader, size)
  if size ~= 8 then
    error("unsupported lua_Number size: " .. tostring(size))
  end
  return decode_double_le(reader:read(size))
end

local function read_string(reader)
  local size = read_size(reader)
  if size == 0 then
    return nil
  end
  size = size - 1
  if size == 0 then
    return ""
  end
  return reader:read(size)
end

local function decode_instruction(word)
  local op = word % 2 ^ SIZE_OP
  local a = floor(word / 2 ^ POS_A) % 2 ^ SIZE_A
  local k = floor(word / 2 ^ POS_k) % 2
  local b = floor(word / 2 ^ POS_B) % 2 ^ SIZE_B
  local c = floor(word / 2 ^ POS_C) % 2 ^ SIZE_C
  local bx = floor(word / 2 ^ POS_Bx) % 2 ^ SIZE_Bx
  local ax = floor(word / 2 ^ POS_Ax) % 2 ^ SIZE_Ax
  local sj = floor(word / 2 ^ POS_sJ) % 2 ^ SIZE_sJ - OFFSET_sJ
  return {
    raw = word,
    op = op,
    name = OPCODES[op],
    a = a,
    b = b,
    c = c,
    k = k,
    bx = bx,
    ax = ax,
    sbx = bx - OFFSET_sBx,
    sb = b - OFFSET_sC,
    sc = c - OFFSET_sC,
    sj = sj,
  }
end

local function parse_header(reader)
  if reader:read(4) ~= LUA_SIGNATURE then
    error("not a Lua chunk")
  end
  if reader:read_byte() ~= LUAC_VERSION then
    error("expected Lua 5.4 bytecode")
  end
  if reader:read_byte() ~= LUAC_FORMAT then
    error("unsupported Lua bytecode format")
  end
  if reader:read(#LUAC_DATA) ~= LUAC_DATA then
    error("corrupted Lua chunk header")
  end
  local instruction_size = reader:read_byte()
  local integer_size = reader:read_byte()
  local number_size = reader:read_byte()
  if instruction_size ~= 4 then
    error("unsupported instruction size: " .. tostring(instruction_size))
  end
  if read_lua_integer(reader, integer_size) ~= LUAC_INT then
    error("Lua integer format mismatch")
  end
  if read_lua_number(reader, number_size) ~= LUAC_NUM then
    error("Lua number format mismatch")
  end
  return {
    instruction_size = instruction_size,
    integer_size = integer_size,
    number_size = number_size,
    main_nups = reader:read_byte(),
  }
end

local function load_function(reader, state, parent_source)
  local proto = {}
  proto.source = read_string(reader) or parent_source
  proto.linedefined = read_int(reader)
  proto.lastlinedefined = read_int(reader)
  proto.numparams = reader:read_byte()
  proto.is_vararg = reader:read_byte() ~= 0
  proto.maxstacksize = reader:read_byte()

  local code_count = read_int(reader)
  proto.code = {}
  for i = 1, code_count do
    proto.code[i] = decode_instruction(bytes_to_uint_le(reader:read(state.instruction_size)))
  end

  local constant_count = read_int(reader)
  proto.constants = {}
  for i = 1, constant_count do
    local tag = reader:read_byte()
    if tag == LUA_VNIL then
      proto.constants[i] = nil
    elseif tag == LUA_VFALSE then
      proto.constants[i] = false
    elseif tag == LUA_VTRUE then
      proto.constants[i] = true
    elseif tag == LUA_VNUMINT then
      proto.constants[i] = read_lua_integer(reader, state.integer_size)
    elseif tag == LUA_VNUMFLT then
      proto.constants[i] = read_lua_number(reader, state.number_size)
    elseif tag == LUA_VSHRSTR or tag == LUA_VLNGSTR then
      proto.constants[i] = read_string(reader)
    else
      error("unsupported constant tag: " .. tostring(tag))
    end
  end

  local upvalue_count = read_int(reader)
  proto.upvalues = {}
  for i = 1, upvalue_count do
    proto.upvalues[i] = {
      instack = reader:read_byte() ~= 0,
      idx = reader:read_byte(),
      kind = reader:read_byte(),
    }
  end

  local proto_count = read_int(reader)
  proto.protos = {}
  for i = 1, proto_count do
    proto.protos[i] = load_function(reader, state, proto.source)
  end

  local lineinfo_count = read_int(reader)
  proto.lineinfo = {}
  for i = 1, lineinfo_count do
    proto.lineinfo[i] = reader:read_byte()
  end

  local absline_count = read_int(reader)
  proto.abslineinfo = {}
  for i = 1, absline_count do
    proto.abslineinfo[i] = { pc = read_int(reader), line = read_int(reader) }
  end

  local local_count = read_int(reader)
  proto.locals = {}
  for i = 1, local_count do
    proto.locals[i] = { name = read_string(reader), startpc = read_int(reader), endpc = read_int(reader) }
  end

  local upname_count = read_int(reader)
  for i = 1, upname_count do
    if proto.upvalues[i] then
      proto.upvalues[i].name = read_string(reader)
    else
      read_string(reader)
    end
  end

  return proto
end

function M.load_bytecode(bytecode)
  local reader = Reader.new(bytecode)
  local state = parse_header(reader)
  local proto = load_function(reader, state)
  proto.main_nups = state.main_nups
  return proto
end

local function metafield(value, name)
  local mt = getmetatable(value)
  return mt and mt[name] or nil
end

local function get_metatable_chain(value, event)
  return metafield(value, event)
end

local function call_close_method(value, err)
  local closer = metafield(value, "__close")
  if closer then
    return closer(value, err)
  end
  return nil
end

local function tbl_get(object, key)
  if type(object) == "table" then
    local v = object[key]
    if v ~= nil then
      return v
    end
  end
  local mm = get_metatable_chain(object, "__index")
  if mm == nil then
    error("attempt to index a " .. type(object) .. " value")
  end
  if type(mm) == "function" then
    return mm(object, key)
  end
  return tbl_get(mm, key)
end

local function tbl_set(object, key, value)
  if type(object) == "table" then
    if object[key] ~= nil then
      object[key] = value
      return
    end
    local mm = get_metatable_chain(object, "__newindex")
    if mm == nil then
      object[key] = value
      return
    end
    if type(mm) == "function" then
      mm(object, key, value)
    else
      tbl_set(mm, key, value)
    end
    return
  end
  local mm = get_metatable_chain(object, "__newindex")
  if mm == nil then
    error("attempt to index a " .. type(object) .. " value")
  end
  if type(mm) == "function" then
    mm(object, key, value)
  else
    tbl_set(mm, key, value)
  end
end

local function concat_values(values)
  local parts = {}
  for i = 1, #values do
    local v = values[i]
    if type(v) == "string" or type(v) == "number" then
      parts[i] = tostring(v)
    else
      local mm = metafield(v, "__concat")
      if not mm then
        error("attempt to concatenate a " .. type(v) .. " value")
      end
      local result = values[1]
      for j = 2, #values do
        local handler = metafield(result, "__concat") or metafield(values[j], "__concat")
        if not handler then
          error("attempt to concatenate incompatible values")
        end
        result = handler(result, values[j])
      end
      return result
    end
  end
  return concat(parts)
end

local function compare_values(a, b, op)
  if op == "EQ" then
    if a == b then
      return true
    end
    local mm1 = metafield(a, "__eq")
    local mm2 = metafield(b, "__eq")
    if mm1 and mm1 == mm2 then
      return mm1(a, b)
    end
    return false
  elseif op == "LT" then
    if type(a) == type(b) and (type(a) == "number" or type(a) == "string") then
      return a < b
    end
    local mm1 = metafield(a, "__lt")
    local mm2 = metafield(b, "__lt")
    if mm1 and mm1 == mm2 then
      return mm1(a, b)
    end
  elseif op == "LE" then
    if type(a) == type(b) and (type(a) == "number" or type(a) == "string") then
      return a <= b
    end
    local mm1 = metafield(a, "__le")
    local mm2 = metafield(b, "__le")
    if mm1 and mm1 == mm2 then
      return mm1(a, b)
    end
    local lt1 = metafield(a, "__lt")
    local lt2 = metafield(b, "__lt")
    if lt1 and lt1 == lt2 then
      return not lt1(b, a)
    end
  end
  error("attempt to compare incompatible values")
end

local Upvalue = {}
Upvalue.__index = Upvalue

function Upvalue.open(registers, index)
  return setmetatable({ registers = registers, index = index, closed = false, value = nil }, Upvalue)
end

function Upvalue.closed(value)
  return setmetatable({ registers = nil, index = nil, closed = true, value = value }, Upvalue)
end

function Upvalue:get()
  if self.closed then
    return self.value
  end
  return self.registers[self.index]
end

function Upvalue:set(value)
  if self.closed then
    self.value = value
  else
    self.registers[self.index] = value
  end
end

function Upvalue:close()
  if not self.closed then
    self.value = self.registers[self.index]
    self.registers = nil
    self.index = nil
    self.closed = true
  end
end

local Closure = {}
Closure.__index = Closure

function Closure.new(proto, env, upvalues)
  return setmetatable({ proto = proto, env = env, upvalues = upvalues or {} }, Closure)
end

local VM = {}
VM.__index = VM

function VM.new(globals)
  return setmetatable({ globals = globals or _G }, VM)
end

function VM:capture(frame, index)
  local existing = frame.open_upvalues[index]
  if existing then
    return existing
  end
  local upv = Upvalue.open(frame.registers, index)
  frame.open_upvalues[index] = upv
  return upv
end

function VM:close_upvalues(frame, from_index, err)
  local keys = {}
  for index in pairs(frame.open_upvalues) do
    if index >= from_index then
      keys[#keys + 1] = index
    end
  end
  sort(keys, function(a, b) return a > b end)
  for i = 1, #keys do
    local index = keys[i]
    frame.open_upvalues[index]:close()
    frame.open_upvalues[index] = nil
  end
  local to_close = frame.to_close
  local remaining = {}
  for i = 1, #to_close do
    local entry = to_close[i]
    if entry.index >= from_index then
      call_close_method(entry.value, err)
    else
      remaining[#remaining + 1] = entry
    end
  end
  frame.to_close = remaining
end

function VM:call_value(fn, args)
  if getmetatable(fn) == Closure then
    return pack(self:execute(fn, unpack(args, 1, #args)))
  end
  if type(fn) == "function" then
    return pack(fn(unpack(args, 1, #args)))
  end
  local mm = metafield(fn, "__call")
  if not mm then
    error("attempt to call a " .. type(fn) .. " value")
  end
  local call_args = { fn }
  for i = 1, #args do
    call_args[#call_args + 1] = args[i]
  end
  return pack(mm(unpack(call_args, 1, #call_args)))
end

function VM:skip_following_mm(frame)
  local next_ins = frame.proto.code[frame.pc]
  if next_ins and (next_ins.name == "MMBIN" or next_ins.name == "MMBINI" or next_ins.name == "MMBINK") then
    frame.pc = frame.pc + 1
  end
end

function VM:binary_meta(lhs, rhs, event)
  local mm = metafield(lhs, event) or metafield(rhs, event)
  if not mm then
    error("missing metamethod " .. event)
  end
  return mm(lhs, rhs)
end

function VM:arith(frame, a, lhs, rhs, event, primitive)
  if type(lhs) == "number" and type(rhs) == "number" then
    frame.registers[a] = primitive(lhs, rhs)
    self:skip_following_mm(frame)
  else
    frame.registers[a] = self:binary_meta(lhs, rhs, event)
    self:skip_following_mm(frame)
  end
end

function VM:bitwise(frame, a, lhs, rhs, event, primitive)
  if type(lhs) == "number" and type(rhs) == "number" then
    frame.registers[a] = primitive(lhs, rhs)
    self:skip_following_mm(frame)
  else
    frame.registers[a] = self:binary_meta(lhs, rhs, event)
    self:skip_following_mm(frame)
  end
end

function VM:make_closure(proto, env, parent, frame)
  local captured = {}
  for i = 1, #proto.upvalues do
    local desc = proto.upvalues[i]
    if desc.instack then
      captured[i] = self:capture(frame, desc.idx)
    else
      captured[i] = parent.upvalues[desc.idx + 1]
    end
  end
  return Closure.new(proto, env, captured)
end

function VM:load_ranged(registers, first, count)
  local out = {}
  for i = 0, count - 1 do
    out[#out + 1] = registers[first + i]
  end
  return out
end

function VM:rk(frame, index, use_const)
  if use_const ~= 0 then
    return frame.proto.constants[index + 1]
  end
  return frame.registers[index]
end

function VM:set_results(frame, base, results, count_field)
  if count_field == 0 then
    for i = 1, results.n do
      frame.registers[base + i - 1] = results[i]
    end
    frame.top = base + results.n
  else
    local wanted = count_field - 1
    for i = 1, wanted do
      frame.registers[base + i - 1] = results[i]
    end
  end
end

function VM:execute(closure, ...)
  local args = pack(...)
  local proto = closure.proto
  local registers = {}
  local frame = {
    closure = closure,
    proto = proto,
    registers = registers,
    open_upvalues = {},
    to_close = {},
    pc = 1,
    top = proto.maxstacksize,
    varargs = {},
  }

  for i = 0, proto.numparams - 1 do
    registers[i] = args[i + 1]
  end
  if proto.is_vararg then
    for i = proto.numparams + 1, args.n do
      frame.varargs[#frame.varargs + 1] = args[i]
    end
  end

  while true do
    local ins = proto.code[frame.pc]
    if not ins then
      self:close_upvalues(frame, 0)
      return
    end
    frame.pc = frame.pc + 1
    local a = ins.a
    local r = frame.registers

    if ins.name == "MOVE" then
      r[a] = r[ins.b]

    elseif ins.name == "LOADI" then
      r[a] = ins.sbx

    elseif ins.name == "LOADF" then
      r[a] = ins.sbx

    elseif ins.name == "LOADK" then
      r[a] = proto.constants[ins.bx + 1]

    elseif ins.name == "LOADKX" then
      local extra = proto.code[frame.pc]
      frame.pc = frame.pc + 1
      r[a] = proto.constants[extra.ax + 1]

    elseif ins.name == "LOADFALSE" then
      r[a] = false

    elseif ins.name == "LFALSESKIP" then
      r[a] = false
      frame.pc = frame.pc + 1

    elseif ins.name == "LOADTRUE" then
      r[a] = true

    elseif ins.name == "LOADNIL" then
      for i = 0, ins.b do
        r[a + i] = nil
      end

    elseif ins.name == "GETUPVAL" then
      r[a] = closure.upvalues[ins.b + 1]:get()

    elseif ins.name == "SETUPVAL" then
      closure.upvalues[ins.b + 1]:set(r[a])

    elseif ins.name == "GETTABUP" then
      local up = closure.upvalues[ins.b + 1]:get()
      r[a] = tbl_get(up, proto.constants[ins.c + 1])

    elseif ins.name == "GETTABLE" then
      r[a] = tbl_get(r[ins.b], r[ins.c])

    elseif ins.name == "GETI" then
      r[a] = tbl_get(r[ins.b], ins.c)

    elseif ins.name == "GETFIELD" then
      r[a] = tbl_get(r[ins.b], proto.constants[ins.c + 1])

    elseif ins.name == "SETTABUP" then
      local up = closure.upvalues[a + 1]:get()
      tbl_set(up, proto.constants[ins.b + 1], self:rk(frame, ins.c, ins.k))

    elseif ins.name == "SETTABLE" then
      tbl_set(r[a], r[ins.b], self:rk(frame, ins.c, ins.k))

    elseif ins.name == "SETI" then
      tbl_set(r[a], ins.b, self:rk(frame, ins.c, ins.k))

    elseif ins.name == "SETFIELD" then
      tbl_set(r[a], proto.constants[ins.b + 1], self:rk(frame, ins.c, ins.k))

    elseif ins.name == "NEWTABLE" then
      local t = {}
      r[a] = t
      if ins.k ~= 0 then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "SELF" then
      local obj = r[ins.b]
      r[a + 1] = obj
      r[a] = tbl_get(obj, self:rk(frame, ins.c, ins.k))

    elseif ins.name == "ADDI" then
      self:arith(frame, a, r[ins.b], ins.sc, "__add", function(x, y) return x + y end)

    elseif ins.name == "ADDK" then
      self:arith(frame, a, r[ins.b], proto.constants[ins.c + 1], "__add", function(x, y) return x + y end)

    elseif ins.name == "SUBK" then
      self:arith(frame, a, r[ins.b], proto.constants[ins.c + 1], "__sub", function(x, y) return x - y end)

    elseif ins.name == "MULK" then
      self:arith(frame, a, r[ins.b], proto.constants[ins.c + 1], "__mul", function(x, y) return x * y end)

    elseif ins.name == "MODK" then
      self:arith(frame, a, r[ins.b], proto.constants[ins.c + 1], "__mod", function(x, y) return x % y end)

    elseif ins.name == "POWK" then
      self:arith(frame, a, r[ins.b], proto.constants[ins.c + 1], "__pow", function(x, y) return x ^ y end)

    elseif ins.name == "DIVK" then
      self:arith(frame, a, r[ins.b], proto.constants[ins.c + 1], "__div", function(x, y) return x / y end)

    elseif ins.name == "IDIVK" then
      self:arith(frame, a, r[ins.b], proto.constants[ins.c + 1], "__idiv", idiv)

    elseif ins.name == "BANDK" then
      self:bitwise(frame, a, r[ins.b], proto.constants[ins.c + 1], "__band", bit_and)

    elseif ins.name == "BORK" then
      self:bitwise(frame, a, r[ins.b], proto.constants[ins.c + 1], "__bor", bit_or)

    elseif ins.name == "BXORK" then
      self:bitwise(frame, a, r[ins.b], proto.constants[ins.c + 1], "__bxor", bit_xor)

    elseif ins.name == "SHRI" then
      self:bitwise(frame, a, r[ins.b], ins.sc, "__shr", shift_right)

    elseif ins.name == "SHLI" then
      self:bitwise(frame, a, ins.sc, r[ins.b], "__shl", shift_left)

    elseif ins.name == "ADD" then
      self:arith(frame, a, r[ins.b], r[ins.c], "__add", function(x, y) return x + y end)

    elseif ins.name == "SUB" then
      self:arith(frame, a, r[ins.b], r[ins.c], "__sub", function(x, y) return x - y end)

    elseif ins.name == "MUL" then
      self:arith(frame, a, r[ins.b], r[ins.c], "__mul", function(x, y) return x * y end)

    elseif ins.name == "MOD" then
      self:arith(frame, a, r[ins.b], r[ins.c], "__mod", function(x, y) return x % y end)

    elseif ins.name == "POW" then
      self:arith(frame, a, r[ins.b], r[ins.c], "__pow", function(x, y) return x ^ y end)

    elseif ins.name == "DIV" then
      self:arith(frame, a, r[ins.b], r[ins.c], "__div", function(x, y) return x / y end)

    elseif ins.name == "IDIV" then
      self:arith(frame, a, r[ins.b], r[ins.c], "__idiv", idiv)

    elseif ins.name == "BAND" then
      self:bitwise(frame, a, r[ins.b], r[ins.c], "__band", bit_and)

    elseif ins.name == "BOR" then
      self:bitwise(frame, a, r[ins.b], r[ins.c], "__bor", bit_or)

    elseif ins.name == "BXOR" then
      self:bitwise(frame, a, r[ins.b], r[ins.c], "__bxor", bit_xor)

    elseif ins.name == "SHL" then
      self:bitwise(frame, a, r[ins.b], r[ins.c], "__shl", shift_left)

    elseif ins.name == "SHR" then
      self:bitwise(frame, a, r[ins.b], r[ins.c], "__shr", shift_right)

    elseif ins.name == "MMBIN" then
      local event = TM_EVENTS[ins.c]
      r[a] = self:binary_meta(r[a], r[ins.b], event)

    elseif ins.name == "MMBINI" then
      local event = TM_EVENTS[ins.c]
      if ins.k ~= 0 then
        r[a] = self:binary_meta(ins.sb, r[a], event)
      else
        r[a] = self:binary_meta(r[a], ins.sb, event)
      end

    elseif ins.name == "MMBINK" then
      local event = TM_EVENTS[ins.c]
      local kv = proto.constants[ins.b + 1]
      if ins.k ~= 0 then
        r[a] = self:binary_meta(kv, r[a], event)
      else
        r[a] = self:binary_meta(r[a], kv, event)
      end

    elseif ins.name == "UNM" then
      local v = r[ins.b]
      if type(v) == "number" then
        r[a] = -v
      else
        local mm = metafield(v, "__unm")
        if not mm then error("attempt to negate a " .. type(v) .. " value") end
        r[a] = mm(v)
      end

    elseif ins.name == "BNOT" then
      local v = r[ins.b]
      if type(v) == "number" then
        r[a] = bit_not(v)
      else
        local mm = metafield(v, "__bnot")
        if not mm then error("attempt to bitwise-not a " .. type(v) .. " value") end
        r[a] = mm(v)
      end

    elseif ins.name == "NOT" then
      r[a] = is_false(r[ins.b])

    elseif ins.name == "LEN" then
      local v = r[ins.b]
      local mm = metafield(v, "__len")
      r[a] = mm and mm(v) or #v

    elseif ins.name == "CONCAT" then
      local values = {}
      for i = 0, ins.b - 1 do
        values[#values + 1] = r[a + i]
      end
      r[a] = concat_values(values)

    elseif ins.name == "CLOSE" then
      self:close_upvalues(frame, a)

    elseif ins.name == "TBC" then
      frame.to_close[#frame.to_close + 1] = { index = a, value = r[a] }

    elseif ins.name == "JMP" then
      frame.pc = frame.pc + ins.sj

    elseif ins.name == "EQ" then
      if compare_values(r[a], r[ins.b], "EQ") ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "LT" then
      if compare_values(r[a], r[ins.b], "LT") ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "LE" then
      if compare_values(r[a], r[ins.b], "LE") ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "EQK" then
      if compare_values(r[a], proto.constants[ins.b + 1], "EQ") ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "EQI" then
      if compare_values(r[a], ins.sb, "EQ") ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "LTI" then
      if compare_values(r[a], ins.sb, "LT") ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "LEI" then
      if compare_values(r[a], ins.sb, "LE") ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "GTI" then
      if compare_values(ins.sb, r[a], "LT") ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "GEI" then
      if compare_values(ins.sb, r[a], "LE") ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "TEST" then
      if (not is_false(r[a])) ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif ins.name == "TESTSET" then
      local value = r[ins.b]
      if (not is_false(value)) ~= (ins.k ~= 0) then
        frame.pc = frame.pc + 1
      else
        r[a] = value
      end

    elseif ins.name == "CALL" or ins.name == "TAILCALL" then
      local arg_count = ins.b == 0 and (frame.top - a) or ins.b
      local args_list = {}
      for i = 1, arg_count - 1 do
        args_list[i] = r[a + i]
      end
      local results = self:call_value(r[a], args_list)
      if ins.name == "TAILCALL" then
        self:close_upvalues(frame, 0)
        return unpack(results, 1, results.n)
      end
      self:set_results(frame, a, results, ins.c)

    elseif ins.name == "RETURN" then
      local out = {}
      if ins.b == 0 then
        for i = a, frame.top - 1 do
          out[#out + 1] = r[i]
        end
      else
        for i = 0, ins.b - 2 do
          out[#out + 1] = r[a + i]
        end
      end
      self:close_upvalues(frame, 0)
      return unpack(out, 1, #out)

    elseif ins.name == "RETURN0" then
      self:close_upvalues(frame, 0)
      return

    elseif ins.name == "RETURN1" then
      self:close_upvalues(frame, 0)
      return r[a]

    elseif ins.name == "FORPREP" then
      local init = tonumber(r[a])
      local limit = tonumber(r[a + 1])
      local step = tonumber(r[a + 2])
      if not init or not limit or not step then
        error("numeric for loop requires numbers")
      end
      local next_value = init
      local run = step > 0 and next_value <= limit or step < 0 and next_value >= limit
      if not run then
        frame.pc = frame.pc + ins.bx + 1
      else
        r[a] = init - step
      end

    elseif ins.name == "FORLOOP" then
      local step = r[a + 2]
      local idx = r[a] + step
      r[a] = idx
      local limit = r[a + 1]
      local ok = step > 0 and idx <= limit or step < 0 and idx >= limit
      if ok then
        r[a + 3] = idx
        frame.pc = frame.pc - ins.bx
      end

    elseif ins.name == "TFORPREP" then
      frame.pc = frame.pc + ins.bx

    elseif ins.name == "TFORCALL" then
      local results = self:call_value(r[a], { r[a + 1], r[a + 2] })
      for i = 1, ins.c do
        r[a + 3 + i] = results[i]
      end
      frame.top = a + 4 + ins.c

    elseif ins.name == "TFORLOOP" then
      if r[a + 2] ~= nil then
        r[a] = r[a + 2]
        frame.pc = frame.pc - ins.bx
      end

    elseif ins.name == "SETLIST" then
      local count = ins.b
      if count == 0 then
        count = frame.top - a - 1
      end
      local start_index = ins.c
      if ins.k ~= 0 then
        local extra = proto.code[frame.pc]
        frame.pc = frame.pc + 1
        start_index = start_index * 2 ^ 25 + extra.ax
      end
      local t = r[a]
      for i = 1, count do
        t[start_index + i] = r[a + i]
      end

    elseif ins.name == "CLOSURE" then
      r[a] = self:make_closure(proto.protos[ins.bx + 1], closure.env, closure, frame)

    elseif ins.name == "VARARG" then
      if ins.c == 0 then
        for i = 1, #frame.varargs do
          r[a + i - 1] = frame.varargs[i]
        end
        frame.top = a + #frame.varargs
      else
        for i = 1, ins.c - 1 do
          r[a + i - 1] = frame.varargs[i]
        end
      end

    elseif ins.name == "VARARGPREP" then
      -- Lua 5.4 uses this to normalize stack layout for vararg functions.
      -- This interpreter stores fixed args and varargs separately already, so
      -- there is nothing extra to do here.

    elseif ins.name == "EXTRAARG" then
      -- consumed by the previous instruction

    else
      error("unsupported opcode: " .. tostring(ins.name))
    end
  end
end

function M.new_vm(globals)
  return VM.new(globals)
end

function M.load(bytecode, globals)
  local proto = M.load_bytecode(bytecode)
  local vm = VM.new(globals)
  local upvalues = {}
  local main_upcount = proto.main_nups or #proto.upvalues
  for i = 1, max(main_upcount, #proto.upvalues) do
    local desc = proto.upvalues[i]
    if desc and desc.name == "_ENV" then
      upvalues[i] = Upvalue.closed(globals or vm.globals)
    else
      upvalues[i] = Upvalue.closed(nil)
    end
  end
  local closure = Closure.new(proto, globals or vm.globals, upvalues)
  return function(...)
    return vm:execute(closure, ...)
  end, proto, vm
end

function M.run(bytecode, globals, ...)
  local fn = M.load(bytecode, globals)
  return fn(...)
end

if ... == nil then
  print("Lua 5.4 bytecode interpreter module loaded.")
  print("Use M.load(bytecode) or M.run(bytecode, globals, ...) with a Lua 5.4 binary chunk.")
end

return M
