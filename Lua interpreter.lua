-- Luau-style BYTECODE interpreter in Lua 5.1-compatible code.
--
-- This VM does NOT parse source text. It executes a chunk represented as
-- bytecode-like instruction tables.
--
-- Public API:
--   local VM = dofile("Lua interpreter.lua")
--   local vm = VM.new_vm()
--   local result = vm:run(chunk)
--
-- Chunk shape:
-- {
--   constants = { ... },
--   protos = { <nested chunk>, ... },
--   code = {
--     { op="LOADK", a=0, bx=1 },
--     { op="RETURN", a=0 },
--   }
-- }

local M = {}

local unpack = unpack or table.unpack

local function copy_args(...)
  return { n = select("#", ...), ... }
end

local function resolve_label_map(code)
  local labels = {}
  for pc = 1, #code do
    local ins = code[pc]
    if ins.label then
      labels[ins.label] = pc
    end
  end
  return labels
end

local function jump_target(pc, ins, labels)
  if ins.target then
    local t = labels[ins.target]
    if not t then error("unknown jump label: " .. tostring(ins.target)) end
    return t
  end
  if ins.sbx then return pc + ins.sbx end
  error("jump instruction missing target/sbx")
end

local VM = {}
VM.__index = VM

function VM.new(globals)
  local self = setmetatable({}, VM)
  self.globals = globals or {
    print = print,
    tostring = tostring,
    tonumber = tonumber,
    type = type,
    math = math,
    string = string,
    table = table,
    pairs = pairs,
    ipairs = ipairs,
  }
  return self
end

function VM:exec(proto, env, upvalues)
  local code = proto.code or {}
  local k = proto.constants or {}
  local p = proto.protos or {}
  local labels = resolve_label_map(code)

  local regs = {}
  local pc = 1

  local function rval(spec)
    if not spec then return nil end
    local kind = spec.kind
    if kind == "reg" then return regs[spec.idx]
    elseif kind == "const" then return k[spec.idx]
    elseif kind == "up" then return upvalues and upvalues[spec.idx] or nil
    elseif kind == "global" then return env[spec.name]
    end
    error("bad operand kind: " .. tostring(kind))
  end

  local function set_up(i, v)
    if not upvalues then upvalues = {} end
    upvalues[i] = v
  end

  while true do
    local ins = code[pc]
    if not ins then return nil end

    local op = ins.op

    if op == "MOVE" then
      regs[ins.a] = regs[ins.b]
      pc = pc + 1

    elseif op == "LOADK" then
      regs[ins.a] = k[ins.bx]
      pc = pc + 1

    elseif op == "LOADBOOL" then
      regs[ins.a] = not not ins.b
      pc = pc + 1

    elseif op == "LOADNIL" then
      for i = ins.a, ins.b do regs[i] = nil end
      pc = pc + 1

    elseif op == "GETGLOBAL" then
      regs[ins.a] = env[ins.k]
      pc = pc + 1

    elseif op == "SETGLOBAL" then
      env[ins.k] = regs[ins.a]
      pc = pc + 1

    elseif op == "GETUPVAL" then
      regs[ins.a] = upvalues and upvalues[ins.b] or nil
      pc = pc + 1

    elseif op == "SETUPVAL" then
      set_up(ins.b, regs[ins.a])
      pc = pc + 1

    elseif op == "NEWTABLE" then
      regs[ins.a] = {}
      pc = pc + 1

    elseif op == "GETTABLE" then
      local t = regs[ins.b]
      regs[ins.a] = t and t[rval(ins.c)] or nil
      pc = pc + 1

    elseif op == "SETTABLE" then
      local t = regs[ins.a]
      if t == nil then error("SETTABLE on nil") end
      t[rval(ins.b)] = rval(ins.c)
      pc = pc + 1

    elseif op == "ADD" then regs[ins.a] = rval(ins.b) + rval(ins.c); pc = pc + 1
    elseif op == "SUB" then regs[ins.a] = rval(ins.b) - rval(ins.c); pc = pc + 1
    elseif op == "MUL" then regs[ins.a] = rval(ins.b) * rval(ins.c); pc = pc + 1
    elseif op == "DIV" then regs[ins.a] = rval(ins.b) / rval(ins.c); pc = pc + 1
    elseif op == "MOD" then regs[ins.a] = rval(ins.b) % rval(ins.c); pc = pc + 1
    elseif op == "POW" then regs[ins.a] = rval(ins.b) ^ rval(ins.c); pc = pc + 1

    elseif op == "UNM" then
      regs[ins.a] = -regs[ins.b]
      pc = pc + 1

    elseif op == "NOT" then
      regs[ins.a] = not regs[ins.b]
      pc = pc + 1

    elseif op == "LEN" then
      regs[ins.a] = #regs[ins.b]
      pc = pc + 1

    elseif op == "CONCAT" then
      local parts = {}
      for i = ins.b, ins.c do parts[#parts + 1] = tostring(regs[i]) end
      regs[ins.a] = table.concat(parts)
      pc = pc + 1

    elseif op == "JMP" then
      pc = jump_target(pc, ins, labels)

    elseif op == "JMPIF" then
      if regs[ins.a] then pc = jump_target(pc, ins, labels) else pc = pc + 1 end

    elseif op == "JMPIFNOT" then
      if not regs[ins.a] then pc = jump_target(pc, ins, labels) else pc = pc + 1 end

    elseif op == "EQ" then
      local ok = rval(ins.b) == rval(ins.c)
      if ok == not ins.notv then pc = pc + 1 else pc = pc + 2 end

    elseif op == "LT" then
      local ok = rval(ins.b) < rval(ins.c)
      if ok == not ins.notv then pc = pc + 1 else pc = pc + 2 end

    elseif op == "LE" then
      local ok = rval(ins.b) <= rval(ins.c)
      if ok == not ins.notv then pc = pc + 1 else pc = pc + 2 end

    elseif op == "CALL" then
      local fn = regs[ins.a]
      local argc = ins.b
      local args = {}
      for i = 1, argc do args[i] = regs[ins.a + i] end
      local rets = copy_args(fn(unpack(args, 1, argc)))
      local rcount = ins.c
      if rcount == -1 then
        for i = 1, rets.n do regs[ins.a + i - 1] = rets[i] end
      else
        for i = 1, rcount do regs[ins.a + i - 1] = rets[i] end
      end
      pc = pc + 1

    elseif op == "CLOSURE" then
      local child = p[ins.bx]
      if not child then error("invalid proto index: " .. tostring(ins.bx)) end
      local captured = {}
      if ins.capture then
        for i = 1, #ins.capture do
          local c = ins.capture[i]
          if c.kind == "reg" then captured[i] = regs[c.idx]
          elseif c.kind == "up" then captured[i] = upvalues and upvalues[c.idx] or nil
          elseif c.kind == "const" then captured[i] = k[c.idx]
          else error("bad closure capture kind") end
        end
      end
      regs[ins.a] = function(...)
        local child_up = {}
        for i = 1, #captured do child_up[i] = captured[i] end
        local argv = copy_args(...)
        for i = 1, argv.n do
          child_up[(child.numparams or 0) + i] = argv[i]
        end
        return self:exec(child, env, child_up)
      end
      pc = pc + 1

    elseif op == "RETURN" then
      if ins.b and ins.b > 0 then
        if ins.b == 1 then return regs[ins.a] end
        local out = {}
        for i = 0, ins.b - 1 do out[#out + 1] = regs[ins.a + i] end
        return unpack(out)
      end
      return regs[ins.a]

    else
      error("unknown opcode: " .. tostring(op))
    end
  end
end

function VM:run(chunk)
  return self:exec(chunk, self.globals, {})
end

function M.new_vm(globals)
  return VM.new(globals)
end

-- Demo bytecode: computes fib(10) recursively and prints it.
if ... == nil then
  local fib_proto = {
    constants = { 1, 2 },
    protos = {},
    code = {
      { op = "GETUPVAL", a = 0, b = 1 },        -- n
      { op = "LOADK", a = 1, bx = 1 },          -- 1
      { op = "LE", b = {kind="reg", idx=0}, c = {kind="reg", idx=1} },
      { op = "JMP", sbx = 3 },
      { op = "GETUPVAL", a = 2, b = 1 },
      { op = "RETURN", a = 2, b = 1 },
      { op = "GETUPVAL", a = 3, b = 1 },        -- n
      { op = "LOADK", a = 4, bx = 1 },          -- 1
      { op = "SUB", a = 5, b = {kind="reg", idx=3}, c = {kind="reg", idx=4} },
      { op = "GETUPVAL", a = 6, b = 0 },        -- fib
      { op = "MOVE", a = 7, b = 5 },
      { op = "CALL", a = 6, b = 1, c = 1 },
      { op = "GETUPVAL", a = 8, b = 1 },        -- n
      { op = "LOADK", a = 9, bx = 2 },          -- 2
      { op = "SUB", a = 10, b = {kind="reg", idx=8}, c = {kind="reg", idx=9} },
      { op = "GETUPVAL", a = 11, b = 0 },       -- fib
      { op = "MOVE", a = 12, b = 10 },
      { op = "CALL", a = 11, b = 1, c = 1 },
      { op = "ADD", a = 13, b = {kind="reg", idx=6}, c = {kind="reg", idx=11} },
      { op = "RETURN", a = 13, b = 1 },
    }
  }

  local main = {
    constants = { "fib(10)=", 10 },
    protos = { fib_proto },
    code = {
      { op = "CLOSURE", a = 0, bx = 1 },                    -- fib function
      { op = "SETUPVAL", a = 0, b = 0 },                    -- set recursive upvalue fib
      { op = "LOADK", a = 1, bx = 2 },
      { op = "MOVE", a = 2, b = 1 },
      { op = "CALL", a = 0, b = 1, c = 1 },                 -- fib(10)
      { op = "GETGLOBAL", a = 3, k = "print" },
      { op = "LOADK", a = 4, bx = 1 },
      { op = "MOVE", a = 5, b = 0 },
      { op = "CALL", a = 3, b = 2, c = 0 },
      { op = "RETURN", a = 0, b = 1 },
    }
  }

  local vm = M.new_vm()
  local result = vm:run(main)
  print("result:", result)
end

return M
