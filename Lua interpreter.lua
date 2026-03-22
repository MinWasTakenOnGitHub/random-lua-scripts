local M = {}

local unpack = unpack or table.unpack
local math_abs = math.abs
local math_floor = math.floor
local math_huge = math.huge
local string_byte = string.byte
local string_char = string.char
local string_sub = string.sub
local table_concat = table.concat
local table_insert = table.insert
local setmetatable = setmetatable
local getmetatable = getmetatable
local type = type
local tonumber = tonumber
local tostring = tostring
local pairs = pairs
local select = select
local assert = assert
local error = error
local pcall = pcall

local LUA_SIGNATURE = "\27Lua"
local LUA_TNIL = 0
local LUA_TBOOLEAN = 1
local LUA_TNUMBER = 3
local LUA_TSTRING = 4

local BITRK = 131072
local MAXSTACK = 250

local OPCODES = {
  [0] = "MOVE",
  "LOADK",
  "LOADBOOL",
  "LOADNIL",
  "GETUPVAL",
  "GETGLOBAL",
  "GETTABLE",
  "SETGLOBAL",
  "SETUPVAL",
  "SETTABLE",
  "NEWTABLE",
  "SELF",
  "ADD",
  "SUB",
  "MUL",
  "DIV",
  "MOD",
  "POW",
  "UNM",
  "NOT",
  "LEN",
  "CONCAT",
  "JMP",
  "EQ",
  "LT",
  "LE",
  "TEST",
  "TESTSET",
  "CALL",
  "TAILCALL",
  "RETURN",
  "FORLOOP",
  "FORPREP",
  "TFORLOOP",
  "SETLIST",
  "CLOSE",
  "CLOSURE",
  "VARARG",
}

local function pack_results(...)
  return { n = select("#", ...), ... }
end

local function value_range(registers, start_index, count)
  local out = {}
  if count <= 0 then
    return out
  end
  for i = 0, count - 1 do
    out[#out + 1] = registers[start_index + i]
  end
  return out
end

local function adjust_results(results, wanted)
  if wanted == 0 then
    return {}
  end
  if wanted < 0 then
    return results
  end
  local out = {}
  for i = 1, wanted do
    out[i] = results[i]
  end
  return out
end

local Reader = {}
Reader.__index = Reader

function Reader.new(data)
  return setmetatable({ data = data, pos = 1 }, Reader)
end

function Reader:read(count)
  local start_pos = self.pos
  local end_pos = start_pos + count - 1
  local chunk = string_sub(self.data, start_pos, end_pos)
  if #chunk ~= count then
    error("unexpected end of bytecode stream")
  end
  self.pos = end_pos + 1
  return chunk
end

function Reader:read_byte()
  local b = string_byte(self.data, self.pos)
  if not b then
    error("unexpected end of bytecode stream")
  end
  self.pos = self.pos + 1
  return b
end

local function bytes_to_integer(bytes, little_endian)
  local value = 0
  if little_endian then
    for i = #bytes, 1, -1 do
      value = value * 256 + string_byte(bytes, i)
    end
  else
    for i = 1, #bytes do
      value = value * 256 + string_byte(bytes, i)
    end
  end
  return value
end

local function integer_to_signed(value, byte_count)
  local limit = 2 ^ (byte_count * 8)
  local sign = limit / 2
  if value >= sign then
    return value - limit
  end
  return value
end

local function decode_double(bytes, little_endian)
  local ordered = {}
  local i
  if little_endian then
    for i = 1, 8 do
      ordered[i] = string_byte(bytes, i)
    end
  else
    local idx = 1
    for i = 8, 1, -1 do
      ordered[idx] = string_byte(bytes, i)
      idx = idx + 1
    end
  end

  local mantissa = 0
  for i = 1, 6 do
    mantissa = mantissa + ordered[i] * 2 ^ ((i - 1) * 8)
  end
  mantissa = mantissa + (ordered[7] % 16) * 2 ^ 48

  local exponent = math_floor(ordered[8] % 128) * 16 + math_floor(ordered[7] / 16)
  local sign = ordered[8] >= 128 and -1 or 1

  if exponent == 0 then
    if mantissa == 0 then
      return sign == 1 and 0 or -0
    end
    return sign * 2 ^ (-1022) * (mantissa / 2 ^ 52)
  end

  if exponent == 2047 then
    if mantissa == 0 then
      return sign * math_huge
    end
    return 0 / 0
  end

  return sign * 2 ^ (exponent - 1023) * (1 + mantissa / 2 ^ 52)
end

local function encode_instruction(word)
  local opcode = word % 64
  local a = math_floor(word / 64) % 256
  local c = math_floor(word / 16384) % 512
  local b = math_floor(word / 8388608) % 512
  local bx = math_floor(word / 16384)
  return {
    raw = word,
    op = opcode,
    name = OPCODES[opcode],
    a = a,
    b = b,
    c = c,
    bx = bx,
    sbx = bx - 131071,
  }
end

local function parse_header(reader)
  local signature = reader:read(4)
  if signature ~= LUA_SIGNATURE then
    error("not a Lua bytecode chunk")
  end

  local version = reader:read_byte()
  if version ~= 0x51 then
    error("unsupported Lua bytecode version: " .. tostring(version))
  end

  local format = reader:read_byte()
  if format ~= 0 then
    error("unsupported Lua bytecode format: " .. tostring(format))
  end

  local little_endian = reader:read_byte() ~= 0
  local int_size = reader:read_byte()
  local size_t_size = reader:read_byte()
  local instruction_size = reader:read_byte()
  local number_size = reader:read_byte()
  local integral_flag = reader:read_byte()

  if instruction_size ~= 4 then
    error("unsupported instruction size: " .. tostring(instruction_size))
  end
  if integral_flag ~= 0 then
    error("integral-number bytecode chunks are not supported")
  end

  return {
    little_endian = little_endian,
    int_size = int_size,
    size_t_size = size_t_size,
    instruction_size = instruction_size,
    number_size = number_size,
  }
end

local function read_sized_integer(reader, size, header)
  return bytes_to_integer(reader:read(size), header.little_endian)
end

local function read_lua_integer(reader, header)
  return integer_to_signed(read_sized_integer(reader, header.int_size, header), header.int_size)
end

local function read_size_t(reader, header)
  return read_sized_integer(reader, header.size_t_size, header)
end

local function read_number(reader, header)
  if header.number_size ~= 8 then
    error("unsupported Lua number size: " .. tostring(header.number_size))
  end
  return decode_double(reader:read(header.number_size), header.little_endian)
end

local function read_string(reader, header)
  local length = read_size_t(reader, header)
  if length == 0 then
    return nil
  end
  local raw = reader:read(length)
  return string_sub(raw, 1, -2)
end

local function load_function(reader, header, parent_source)
  local proto = {}
  proto.source = read_string(reader, header) or parent_source
  proto.line_defined = read_lua_integer(reader, header)
  proto.last_line_defined = read_lua_integer(reader, header)
  proto.nups = reader:read_byte()
  proto.numparams = reader:read_byte()
  proto.is_vararg = reader:read_byte()
  proto.maxstacksize = reader:read_byte()

  local code_count = read_lua_integer(reader, header)
  proto.code = {}
  for i = 1, code_count do
    proto.code[i] = encode_instruction(read_sized_integer(reader, header.instruction_size, header))
  end

  local constant_count = read_lua_integer(reader, header)
  proto.constants = {}
  for i = 1, constant_count do
    local tag = reader:read_byte()
    if tag == LUA_TNIL then
      proto.constants[i] = nil
    elseif tag == LUA_TBOOLEAN then
      proto.constants[i] = reader:read_byte() ~= 0
    elseif tag == LUA_TNUMBER then
      proto.constants[i] = read_number(reader, header)
    elseif tag == LUA_TSTRING then
      proto.constants[i] = read_string(reader, header)
    else
      error("unsupported constant type tag: " .. tostring(tag))
    end
  end

  local proto_count = read_lua_integer(reader, header)
  proto.protos = {}
  for i = 1, proto_count do
    proto.protos[i] = load_function(reader, header, proto.source)
  end

  local lineinfo_count = read_lua_integer(reader, header)
  proto.lineinfo = {}
  for i = 1, lineinfo_count do
    proto.lineinfo[i] = read_lua_integer(reader, header)
  end

  local local_count = read_lua_integer(reader, header)
  proto.locals = {}
  for i = 1, local_count do
    proto.locals[i] = {
      name = read_string(reader, header),
      startpc = read_lua_integer(reader, header),
      endpc = read_lua_integer(reader, header),
    }
  end

  local upvalue_count = read_lua_integer(reader, header)
  proto.upvalues = {}
  for i = 1, upvalue_count do
    proto.upvalues[i] = read_string(reader, header)
  end

  return proto
end

function M.load_bytecode(bytecode)
  local reader = Reader.new(bytecode)
  local header = parse_header(reader)
  local proto = load_function(reader, header)
  return proto
end

local function is_falsey(value)
  return value == false or value == nil
end

local function get_metafield(value, event)
  local mt = getmetatable(value)
  if mt then
    return mt[event]
  end
  return nil
end

local function binary_metamethod(vm, lhs, rhs, event)
  local mm = get_metafield(lhs, event) or get_metafield(rhs, event)
  if not mm then
    error("attempt to perform arithmetic on incompatible values")
  end
  return mm(lhs, rhs)
end

local function compare_metamethod(lhs, rhs, event)
  local mm1 = get_metafield(lhs, event)
  local mm2 = get_metafield(rhs, event)
  if not mm1 or mm1 ~= mm2 then
    error("attempt to compare incompatible values")
  end
  return mm1(lhs, rhs)
end

local function table_get(vm, object, key)
  if type(object) == "table" then
    local value = object[key]
    if value ~= nil then
      return value
    end
  end
  local index = get_metafield(object, "__index")
  if index == nil then
    error("attempt to index a " .. type(object) .. " value")
  end
  if type(index) == "function" then
    return index(object, key)
  end
  return table_get(vm, index, key)
end

local function table_set(vm, object, key, value)
  if type(object) == "table" and object[key] ~= nil then
    object[key] = value
    return
  end
  local newindex = get_metafield(object, "__newindex")
  if newindex == nil then
    if type(object) ~= "table" then
      error("attempt to index a " .. type(object) .. " value")
    end
    object[key] = value
    return
  end
  if type(newindex) == "function" then
    newindex(object, key, value)
  else
    table_set(vm, newindex, key, value)
  end
end

local function lua_concat(vm, values)
  local buffer = {}
  for i = 1, #values do
    local value = values[i]
    local t = type(value)
    if t == "string" or t == "number" then
      buffer[i] = tostring(value)
    else
      local mm = get_metafield(value, "__concat")
      if mm then
        local result = values[1]
        for j = 2, #values do
          result = mm(result, values[j])
        end
        return result
      end
      error("attempt to concatenate a " .. t .. " value")
    end
  end
  return table_concat(buffer)
end

local function lua_len(value)
  local mm = get_metafield(value, "__len")
  if mm then
    return mm(value)
  end
  return #value
end

local Upvalue = {}
Upvalue.__index = Upvalue

function Upvalue.new_open(registers, index)
  return setmetatable({ store = registers, index = index, closed = false, value = nil }, Upvalue)
end

function Upvalue.new_closed(value)
  return setmetatable({ store = nil, index = nil, closed = true, value = value }, Upvalue)
end

function Upvalue:get()
  if self.closed then
    return self.value
  end
  return self.store[self.index]
end

function Upvalue:set(value)
  if self.closed then
    self.value = value
  else
    self.store[self.index] = value
  end
end

function Upvalue:close()
  if not self.closed then
    self.value = self.store[self.index]
    self.store = nil
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

function VM:wrap(proto, env)
  local closure = Closure.new(proto, env or self.globals, {})
  return function(...)
    return self:execute(closure, ...)
  end
end

function VM:rk(frame, operand)
  if operand >= BITRK then
    return frame.closure.proto.constants[operand - BITRK + 1]
  end
  return frame.registers[operand]
end

function VM:close_upvalues(frame, from_index)
  local open = frame.open_upvalues
  local keys = {}
  for index in pairs(open) do
    if index >= from_index then
      keys[#keys + 1] = index
    end
  end
  table.sort(keys, function(a, b) return a > b end)
  for i = 1, #keys do
    local index = keys[i]
    open[index]:close()
    open[index] = nil
  end
end

function VM:capture_upvalue(frame, register_index)
  local open = frame.open_upvalues
  local upvalue = open[register_index]
  if not upvalue then
    upvalue = Upvalue.new_open(frame.registers, register_index)
    open[register_index] = upvalue
  end
  return upvalue
end

function VM:call_value(fn, args)
  if getmetatable(fn) == Closure then
    return pack_results(self:execute(fn, unpack(args, 1, #args)))
  end
  local mm = nil
  if type(fn) ~= "function" then
    mm = get_metafield(fn, "__call")
    if not mm then
      error("attempt to call a " .. type(fn) .. " value")
    end
    local copy = { fn }
    for i = 1, #args do
      copy[#copy + 1] = args[i]
    end
    return pack_results(mm(unpack(copy, 1, #copy)))
  end
  return pack_results(fn(unpack(args, 1, #args)))
end

function VM:arith(lhs, rhs, event, primitive)
  if type(lhs) == "number" and type(rhs) == "number" then
    return primitive(lhs, rhs)
  end
  return binary_metamethod(self, lhs, rhs, event)
end

function VM:compare(lhs, rhs, op)
  if op == "EQ" then
    if type(lhs) ~= type(rhs) and not (lhs == nil and rhs == nil) then
      return false
    end
    if lhs == rhs then
      return true
    end
    local mm1 = get_metafield(lhs, "__eq")
    local mm2 = get_metafield(rhs, "__eq")
    if mm1 and mm1 == mm2 then
      return mm1(lhs, rhs)
    end
    return false
  elseif op == "LT" then
    if type(lhs) == type(rhs) and (type(lhs) == "number" or type(lhs) == "string") then
      return lhs < rhs
    end
    return compare_metamethod(lhs, rhs, "__lt")
  elseif op == "LE" then
    if type(lhs) == type(rhs) and (type(lhs) == "number" or type(lhs) == "string") then
      return lhs <= rhs
    end
    local mm1 = get_metafield(lhs, "__le")
    local mm2 = get_metafield(rhs, "__le")
    if mm1 and mm1 == mm2 then
      return mm1(lhs, rhs)
    end
    return not compare_metamethod(rhs, lhs, "__lt")
  end
end

function VM:prepare_varargs(frame, fixed_count)
  local out = {}
  for i = fixed_count + 1, frame.arg_count do
    out[#out + 1] = frame.args[i]
  end
  return out
end

function VM:execute(closure, ...)
  local proto = closure.proto
  local args = pack_results(...)
  local registers = {}
  local frame = {
    closure = closure,
    registers = registers,
    args = args,
    arg_count = args.n,
    varargs = {},
    open_upvalues = {},
    pc = 1,
    top = proto.maxstacksize > 0 and proto.maxstacksize or MAXSTACK,
  }

  for i = 0, proto.numparams - 1 do
    registers[i] = args[i + 1]
  end
  if proto.is_vararg ~= 0 then
    frame.varargs = self:prepare_varargs(frame, proto.numparams)
  end

  while true do
    local instruction = proto.code[frame.pc]
    if not instruction then
      self:close_upvalues(frame, 0)
      return
    end

    frame.pc = frame.pc + 1

    local a = instruction.a
    local op = instruction.name

    if op == "MOVE" then
      registers[a] = registers[instruction.b]

    elseif op == "LOADK" then
      registers[a] = proto.constants[instruction.bx + 1]

    elseif op == "LOADBOOL" then
      registers[a] = instruction.b ~= 0
      if instruction.c ~= 0 then
        frame.pc = frame.pc + 1
      end

    elseif op == "LOADNIL" then
      for index = a, instruction.b do
        registers[index] = nil
      end

    elseif op == "GETUPVAL" then
      registers[a] = closure.upvalues[instruction.b + 1]:get()

    elseif op == "GETGLOBAL" then
      registers[a] = closure.env[proto.constants[instruction.bx + 1]]

    elseif op == "GETTABLE" then
      registers[a] = table_get(self, registers[instruction.b], self:rk(frame, instruction.c))

    elseif op == "SETGLOBAL" then
      closure.env[proto.constants[instruction.bx + 1]] = registers[a]

    elseif op == "SETUPVAL" then
      closure.upvalues[instruction.b + 1]:set(registers[a])

    elseif op == "SETTABLE" then
      table_set(self, registers[a], self:rk(frame, instruction.b), self:rk(frame, instruction.c))

    elseif op == "NEWTABLE" then
      registers[a] = {}

    elseif op == "SELF" then
      local object = registers[instruction.b]
      registers[a + 1] = object
      registers[a] = table_get(self, object, self:rk(frame, instruction.c))

    elseif op == "ADD" then
      registers[a] = self:arith(self:rk(frame, instruction.b), self:rk(frame, instruction.c), "__add", function(x, y) return x + y end)

    elseif op == "SUB" then
      registers[a] = self:arith(self:rk(frame, instruction.b), self:rk(frame, instruction.c), "__sub", function(x, y) return x - y end)

    elseif op == "MUL" then
      registers[a] = self:arith(self:rk(frame, instruction.b), self:rk(frame, instruction.c), "__mul", function(x, y) return x * y end)

    elseif op == "DIV" then
      registers[a] = self:arith(self:rk(frame, instruction.b), self:rk(frame, instruction.c), "__div", function(x, y) return x / y end)

    elseif op == "MOD" then
      registers[a] = self:arith(self:rk(frame, instruction.b), self:rk(frame, instruction.c), "__mod", function(x, y) return x % y end)

    elseif op == "POW" then
      registers[a] = self:arith(self:rk(frame, instruction.b), self:rk(frame, instruction.c), "__pow", function(x, y) return x ^ y end)

    elseif op == "UNM" then
      local value = registers[instruction.b]
      if type(value) == "number" then
        registers[a] = -value
      else
        local mm = get_metafield(value, "__unm")
        if not mm then error("attempt to perform unary minus on a " .. type(value) .. " value") end
        registers[a] = mm(value)
      end

    elseif op == "NOT" then
      registers[a] = is_falsey(registers[instruction.b])

    elseif op == "LEN" then
      registers[a] = lua_len(registers[instruction.b])

    elseif op == "CONCAT" then
      registers[a] = lua_concat(self, value_range(registers, instruction.b, instruction.c - instruction.b + 1))

    elseif op == "JMP" then
      frame.pc = frame.pc + instruction.sbx

    elseif op == "EQ" or op == "LT" or op == "LE" then
      local result = self:compare(self:rk(frame, instruction.b), self:rk(frame, instruction.c), op)
      if result ~= (a ~= 0) then
        frame.pc = frame.pc + 1
      end

    elseif op == "TEST" then
      local condition = not is_falsey(registers[a])
      if condition == (instruction.c == 0) then
        frame.pc = frame.pc + 1
      end

    elseif op == "TESTSET" then
      local value = registers[instruction.b]
      local condition = not is_falsey(value)
      if condition == (instruction.c ~= 0) then
        registers[a] = value
      else
        frame.pc = frame.pc + 1
      end

    elseif op == "CALL" or op == "TAILCALL" then
      local arg_count = instruction.b
      local result_count = instruction.c
      local args_list = {}
      if arg_count == 0 then
        for index = a + 1, frame.top - 1 do
          args_list[#args_list + 1] = registers[index]
        end
      else
        for index = 1, arg_count - 1 do
          args_list[index] = registers[a + index]
        end
      end

      local results = self:call_value(registers[a], args_list)
      if op == "TAILCALL" then
        self:close_upvalues(frame, 0)
        return unpack(results, 1, results.n)
      end

      if result_count == 0 then
        for i = 1, results.n do
          registers[a + i - 1] = results[i]
        end
        frame.top = a + results.n
      else
        for i = 1, result_count - 1 do
          registers[a + i - 1] = results[i]
        end
      end

    elseif op == "RETURN" then
      local result_count = instruction.b
      local results = {}
      if result_count == 0 then
        for index = a, frame.top - 1 do
          results[#results + 1] = registers[index]
        end
      else
        for index = 0, result_count - 2 do
          results[#results + 1] = registers[a + index]
        end
      end
      self:close_upvalues(frame, 0)
      return unpack(results, 1, #results)

    elseif op == "FORLOOP" then
      local step = registers[a + 2]
      local index = registers[a] + step
      registers[a] = index
      local limit = registers[a + 1]
      local continue
      if step > 0 then
        continue = index <= limit
      else
        continue = index >= limit
      end
      if continue then
        registers[a + 3] = index
        frame.pc = frame.pc + instruction.sbx
      end

    elseif op == "FORPREP" then
      registers[a] = registers[a] - registers[a + 2]
      frame.pc = frame.pc + instruction.sbx

    elseif op == "TFORLOOP" then
      local generator = registers[a]
      local state = registers[a + 1]
      local control = registers[a + 2]
      local results = self:call_value(generator, { state, control })
      for i = 1, instruction.c do
        registers[a + 2 + i] = results[i]
      end
      if registers[a + 3] ~= nil then
        registers[a + 2] = registers[a + 3]
      else
        frame.pc = frame.pc + 1
      end

    elseif op == "SETLIST" then
      local count = instruction.b
      local block = instruction.c
      if count == 0 then
        count = frame.top - a - 1
      end
      if block == 0 then
        local extra = proto.code[frame.pc]
        frame.pc = frame.pc + 1
        block = extra.raw
      end
      local offset = (block - 1) * 50
      local target = registers[a]
      for i = 1, count do
        target[offset + i] = registers[a + i]
      end

    elseif op == "CLOSE" then
      self:close_upvalues(frame, a)

    elseif op == "CLOSURE" then
      local child = proto.protos[instruction.bx + 1]
      local upvalues = {}
      for i = 1, child.nups do
        local pseudo = proto.code[frame.pc]
        frame.pc = frame.pc + 1
        if pseudo.name == "MOVE" then
          upvalues[i] = self:capture_upvalue(frame, pseudo.b)
        elseif pseudo.name == "GETUPVAL" then
          upvalues[i] = closure.upvalues[pseudo.b + 1]
        else
          error("unexpected upvalue capture opcode: " .. tostring(pseudo.name))
        end
      end
      registers[a] = Closure.new(child, closure.env, upvalues)

    elseif op == "VARARG" then
      local wanted = instruction.b
      if wanted == 0 then
        for i = 1, #frame.varargs do
          registers[a + i - 1] = frame.varargs[i]
        end
        frame.top = a + #frame.varargs
      else
        for i = 1, wanted - 1 do
          registers[a + i - 1] = frame.varargs[i]
        end
      end

    else
      error("unsupported opcode: " .. tostring(op))
    end
  end
end

function M.new_vm(globals)
  return VM.new(globals)
end

function M.load(bytecode, globals)
  local vm = VM.new(globals)
  local proto = M.load_bytecode(bytecode)
  local closure = Closure.new(proto, globals or vm.globals, {})
  return function(...)
    return vm:execute(closure, ...)
  end, proto, vm
end

function M.run(bytecode, globals, ...)
  local fn = M.load(bytecode, globals)
  return fn(...)
end

if ... == nil then
  local vm = M.new_vm()
  local function sample(a, b)
    local sum = 0
    for i = a, b do
      sum = sum + i
    end
    return sum, a * b, tostring(sum)
  end

  local dumped = string.dump(sample)
  local executable, proto = M.load(dumped)
  local x, y, z = executable(3, 8)
  print("proto source:", proto.source or "=(string.dump)")
  print("results:", x, y, z)
end

return M
