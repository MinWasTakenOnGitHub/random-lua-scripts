-- Fast Numberlink pair-connector solver.
--
-- Board format:
--   grid[r][c] = 0 for empty
--   grid[r][c] = positive integer label for endpoints / claimed path cells
--
-- This solver focuses on connecting each numbered pair quickly.
-- It returns as soon as all pairs are connected (it does NOT require filling all zeros).

local Numberlink = {}

local function idx(r, c, w)
  return (r - 1) * w + c
end

local function manhattan_adj(a, b, w)
  local ar = math.floor((a - 1) / w) + 1
  local ac = ((a - 1) % w) + 1
  local br = math.floor((b - 1) / w) + 1
  local bc = ((b - 1) % w) + 1
  return (ar == br and math.abs(ac - bc) == 1) or (ac == bc and math.abs(ar - br) == 1)
end

local function build_neighbors(h, w)
  local n = h * w
  local neighbors = {}
  for i = 1, n do
    neighbors[i] = {}
  end

  for r = 1, h do
    for c = 1, w do
      local p = idx(r, c, w)
      local t = neighbors[p]
      local k = 1
      if r > 1 then t[k] = idx(r - 1, c, w); k = k + 1 end
      if r < h then t[k] = idx(r + 1, c, w); k = k + 1 end
      if c > 1 then t[k] = idx(r, c - 1, w); k = k + 1 end
      if c < w then t[k] = idx(r, c + 1, w); k = k + 1 end
    end
  end
  return neighbors
end

-- Collect legal moves for a specific endpoint.
-- Returns count and a compact move list.
local function gather_moves(board, neighbors, endpoint, other_endpoint, label)
  local out = {}
  local count = 0
  local ns = neighbors[endpoint]
  for i = 1, #ns do
    local p = ns[i]
    local v = board[p]
    if v == 0 then
      count = count + 1
      out[count] = p
    elseif p == other_endpoint and v == label then
      count = count + 1
      out[count] = p -- direct connection move
    end
  end
  return count, out
end

local function clone_grid_from_board(board, h, w)
  local g = {}
  local k = 1
  for r = 1, h do
    local row = {}
    g[r] = row
    for c = 1, w do
      row[c] = board[k]
      k = k + 1
    end
  end
  return g
end

function Numberlink.solve(grid)
  local h = #grid
  if h == 0 then return false, grid end
  local w = #grid[1]
  if w == 0 then return false, grid end

  local n = h * w
  local board = {}

  local endpoints_a = {}
  local endpoints_b = {}
  local labels = {}
  local label_count = 0

  local function ensure_label(label)
    if not labels[label] then
      labels[label] = true
      label_count = label_count + 1
      endpoints_a[label] = 0
      endpoints_b[label] = 0
    end
  end

  do
    local k = 1
    for r = 1, h do
      local row = grid[r]
      if #row ~= w then
        error("non-rectangular grid")
      end
      for c = 1, w do
        local v = row[c]
        if v < 0 then
          error("negative labels are not supported")
        end
        board[k] = v
        if v > 0 then
          ensure_label(v)
          if endpoints_a[v] == 0 then
            endpoints_a[v] = k
          elseif endpoints_b[v] == 0 then
            endpoints_b[v] = k
          end
        end
        k = k + 1
      end
    end
  end

  -- Validate exactly 2 endpoints per label.
  for label, _ in pairs(labels) do
    if endpoints_a[label] == 0 or endpoints_b[label] == 0 then
      error(("label %d does not have exactly two endpoints"):format(label))
    end
  end

  local neighbors = build_neighbors(h, w)

  local connected = {}
  local connected_count = 0
  for label, _ in pairs(labels) do
    if manhattan_adj(endpoints_a[label], endpoints_b[label], w) then
      connected[label] = true
      connected_count = connected_count + 1
    else
      connected[label] = false
    end
  end

  -- Quick fail: any unconnected endpoint with no legal expansion.
  local function quick_dead_end()
    for label, _ in pairs(labels) do
      if not connected[label] then
        local a = endpoints_a[label]
        local b = endpoints_b[label]
        local ca = gather_moves(board, neighbors, a, b, label)
        local cb = gather_moves(board, neighbors, b, a, label)
        if ca == 0 and cb == 0 then
          return true
        end
      end
    end
    return false
  end

  local function search()
    if connected_count == label_count then
      return true
    end

    -- Minimum-remaining-values choice over all active endpoints.
    local best_label = 0
    local best_side = 0 -- 1 => move endpoint_a, 2 => move endpoint_b
    local best_moves = nil
    local best_count = 1 / 0

    for label, _ in pairs(labels) do
      if not connected[label] then
        local a = endpoints_a[label]
        local b = endpoints_b[label]

        local ca, ma = gather_moves(board, neighbors, a, b, label)
        if ca < best_count then
          best_count = ca
          best_label = label
          best_side = 1
          best_moves = ma
          if best_count == 0 then
            return false
          end
          if best_count == 1 then
            -- cannot do better than forced move for this endpoint
          end
        end

        local cb, mb = gather_moves(board, neighbors, b, a, label)
        if cb < best_count then
          best_count = cb
          best_label = label
          best_side = 2
          best_moves = mb
          if best_count == 0 then
            return false
          end
        end
      end
    end

    if best_label == 0 then
      return false
    end

    local label = best_label
    local e1, e2
    if best_side == 1 then
      e1 = endpoints_a[label]
      e2 = endpoints_b[label]
    else
      e1 = endpoints_b[label]
      e2 = endpoints_a[label]
    end

    -- Try moves; prioritize immediate connection first.
    local immediate = nil
    for i = 1, best_count do
      if best_moves[i] == e2 then
        immediate = i
        break
      end
    end

    local function apply_move(np)
      if np == e2 then
        connected[label] = true
        connected_count = connected_count + 1

        local ok = search()

        connected[label] = false
        connected_count = connected_count - 1
        return ok
      else
        board[np] = label
        if best_side == 1 then
          endpoints_a[label] = np
        else
          endpoints_b[label] = np
        end

        local ok = true
        if quick_dead_end() then
          ok = false
        else
          ok = search()
        end

        if best_side == 1 then
          endpoints_a[label] = e1
        else
          endpoints_b[label] = e1
        end
        board[np] = 0
        return ok
      end
    end

    if immediate then
      if apply_move(best_moves[immediate]) then
        return true
      end
    end

    for i = 1, best_count do
      if i ~= immediate then
        if apply_move(best_moves[i]) then
          return true
        end
      end
    end

    return false
  end

  if quick_dead_end() then
    return false, grid
  end

  local solved = search()
  if not solved then
    return false, grid
  end

  return true, clone_grid_from_board(board, h, w)
end

-- Optional CLI demo usage:
--   lua random_pick.lua
if ... == nil then
  local sample = {
    {1, 0, 0, 2},
    {0, 0, 0, 0},
    {0, 0, 0, 0},
    {1, 0, 0, 2},
  }

  local ok, solved = Numberlink.solve(sample)
  print("Solved:", ok)
  if ok then
    for r = 1, #solved do
      local row = solved[r]
      io.write(table.concat(row, " "), "\n")
    end
  end
end

return Numberlink
