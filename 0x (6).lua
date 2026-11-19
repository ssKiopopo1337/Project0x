-- @author 0x
-- @uid 0
-- 0x 4.6: standalone Neverwin compatibility port of Power Plus.
-- Upstream: ssKiopopo1337/Project0x @ 62e7e32cdf9364efd130156523ccb3efbc5073f7
-- Credits: @kukluxk, @likvidatorchaes (subcult).
-- API: PbLJk/neverlose-lua-api, docs/legacy-api.md. LuaJIT 2.1 / Lua 5.1.

local META = {
    version = "4.6", schema = 7,
    settings = "0x_v46_settings", previous = { "0x_v45_settings", "0x_v4_settings" },
    learned = "0x_resolver_v21", journal = "0x_v46_journal",
    import = "0x_import", export = "0x_export"
}

local K = {
    HISTORY = 96, WINDOW = 0.375, STALE = 0.26, LINGER = 0.35,
    BASE_INTERVAL = 1 / 64, SWITCH_TIME = 0.028, REVEAL = 0.04, LC_HOLD = 0.20,
    JITTER_STEP = 12, STATIC_RATE = 3 * 64, SWAY_RATE = 10 * 64, SPIN_RATE = 20 * 64,
    HINT_EVERY = 0.0625, HB_TTL = 0.8, PURGE_EVERY = 5, PURGE_AGE = 90,
    RECORD_MAX = 128, DB_MAX = 64, TRIED_MAX = 16, TRIED_TTL = 20,
    INTENT_MAX = 16, INTENT_AGE = 0.22, PENDING_MAX = 32, CLOCK_SLOP = 0.025,
    MAX_TARGETS = 3, EVAL_EVERY = 0.0625, WATCHDOG = 0.5,
    RETRY = 5, CMD_MIN = 1, CMD_MAX = 90, RAY_LENGTH = 8192,
    HEAD = 1, CHEST = 2, STOMACH = 3
}

local E = {
    ADAPTIVE = 1, STATIC = 2, BRUTE = 3, JITSPIN = 4, OFFSET = 5,
    CENTER = 1, PREDICT = 2, FOLLOW = 3,
    AUTO = 1, EYE = 2, TARGET = 3, STEP = 2
}

local BRUTE = { 1, -1, 0.5, -0.5, 0, 0.75, -0.75 }
local STEPS = { 0, 1, -1, 2, -2 }
local SINGLE_ZERO, SINGLE_FULL = { 0 }, { 1 }
local JITTER = { [E.CENTER] = { 0, 1, -1, 0.5, -0.5 }, [E.PREDICT] = { 1, -1, 0, 0.5, -0.5 } }
local HINTS = { "body", "freestand", "move_mem", "move_dir" }
local WEIGHTS = { 0.55, 0.40, 0.30, 0.30 }

local CFG, UI = {}, {}
local U, Model, HB, Schema, Store, RES, CMD, Feedback = {}, {}, {}, {}, {}, {}, {}, {}
local Journal, RB, Menu, IO, VIS, LIFE = {}, {}, {}, {}, {}, {}
local S = { rt = 0, epoch = 0, active = false, menu = false, last_cmd = -math.huge, reports = {} }

local abs, floor, min, max, sqrt = math.abs, math.floor, math.min, math.max, math.sqrt
local cos, sin, rad, deg, atan2 = math.cos, math.sin, math.rad, math.deg, math.atan2
local format, lower, sort, remove = string.format, string.lower, table.sort, table.remove

function U.safe(fn, ...)
    if type(fn) ~= "function" then return nil end
    local ok, value = pcall(fn, ...)
    if ok then return value end
end

local function invoke(object, name, ...)
    return object[name](object, ...)
end

function U.call(object, name, ...)
    if object == nil then return nil end
    return U.safe(invoke, object, name, ...)
end

function U.finite(v) return type(v) == "number" and v == v and abs(v) < math.huge end
function U.int(v) return U.finite(v) and v % 1 == 0 end
function U.bound(v, lo, hi) return max(lo, min(hi, v)) end
function U.sign(v) return v > 0 and 1 or (v < 0 and -1 or 0) end
function U.wrap(v) return (v + 180) % 360 - 180 end
function U.round(v) return floor(v + 0.5) end
function U.vec(v) return type(v) == "table" and U.finite(v.x) and U.finite(v.y) and U.finite(v.z) end
function U.ptr(v) return U.int(v) and v >= 65536 and v <= 140737488355327 end
function U.addr(ent)
    local v = U.call(ent, "address")
    if U.ptr(v) then return v end
end

function U.copy(v)
    if type(v) ~= "table" then return v end
    local out = {}
    for k, item in pairs(v) do out[k] = item end
    return out
end

function U.same(a, b)
    if a == b then return true end
    if U.finite(a) and U.finite(b) then return abs(a - b) <= 0.0001 end
    if type(a) ~= "table" or type(b) ~= "table" then return false end
    for k, v in pairs(a) do if b[k] ~= v then return false end end
    for k in pairs(b) do if a[k] == nil then return false end end
    return true
end

function U.interval()
    local v = U.safe(globals.interval)
    return U.finite(v) and v >= 1 / 256 and v <= 1 / 16 and v or K.BASE_INTERVAL
end

function U.you(ent, key)
    if not ent then return false end
    if U.call(ent, "is_local") == true then return true end
    local a = U.addr(ent)
    return a ~= nil and a == U.addr(U.safe(entity[key]))
end

function U.yaw(a, b) return deg(atan2(b.y - a.y, b.x - a.x)) end
function U.fov(a, b, va)
    local dx, dy, dz = b.x - a.x, b.y - a.y, b.z - a.z
    local p = deg(atan2(-dz, sqrt(dx * dx + dy * dy))) - va.x
    local y = U.wrap(deg(atan2(dy, dx)) - va.y)
    return sqrt(p * p + y * y)
end

function U.yaw_equal(a, b, eps)
    return U.vec(a) and U.vec(b) and abs(U.wrap(a.y - b.y)) <= eps and abs(a.x - b.x) <= eps
end

function U.age(then_rt, now)
    if not then_rt then return math.huge end
    local dt = now - then_rt
    return dt >= -K.CLOCK_SLOP and dt or math.huge
end

function U.say(message) print("[0x] " .. tostring(message)) end
function U.report(where, err)
    local at = S.reports[where]
    if at and U.age(at, S.rt) < K.RETRY then return end
    S.reports[where] = S.rt
    U.say(where .. ": " .. tostring(err))
end

function U.guard(where, fn, ...)
    local ok, result = pcall(fn, ...)
    if not ok then U.report(where, result) end
    return ok, result
end

function U.weapon_name(name)
    if type(name) ~= "string" then return nil end
    name = lower(name):gsub("^weapon_", "")
    if #name <= 48 and name:match("^[a-z0-9_]+$") then return name end
end

local WEAPON_GROUP = {
    [40] = 1, [9] = 2, [11] = 3, [38] = 3, [1] = 4, [64] = 4,
    [2] = 5, [3] = 5, [4] = 5, [30] = 5, [32] = 5, [36] = 5,
    [61] = 5, [63] = 5
}

function U.weapon(pawn)
    local info = U.call(pawn, "weapon_info")
    if type(info) ~= "table" then info = U.call(U.call(pawn, "weapon"), "weapon_info") end
    if type(info) == "table" and info.gun == true and info.def ~= 31 then return info end
end

-- Yaw classification uses a bounded ring measured in simulation seconds, not samples per tick.
function Model.reset(rec)
    rec.hist_n, rec.hist_head, rec.hist_time = 0, 0, 0
    rec.class = { name = "static", confidence = 0 }
    rec.candidate, rec.class_since, rec.pitch_flick = nil, nil, 0
    rec.correction, rec.raw, rec.sample_rt = nil, nil, nil
    rec.sample_tick, rec.sample_sim = nil, nil
end

function Model.at(rec, i)
    return rec.history[(rec.hist_head - rec.hist_n + i - 1) % K.HISTORY + 1]
end

function Model.push(rec, yaw, pitch, dt)
    if rec.hist_n > 0 then
        local previous = Model.at(rec, rec.hist_n)
        local gain = abs(previous.pitch - pitch) > 45 and 22 or -12
        rec.pitch_flick = U.bound(rec.pitch_flick + gain * dt, 0, 1)
    end
    rec.hist_time = rec.hist_time + dt
    rec.hist_head = rec.hist_head % K.HISTORY + 1
    rec.hist_n = min(K.HISTORY, rec.hist_n + 1)
    local a = rec.history[rec.hist_head] or {}
    a.yaw, a.pitch, a.t = yaw, pitch, rec.hist_time
    rec.history[rec.hist_head] = a
    while rec.hist_n > 1 and rec.hist_time - Model.at(rec, 1).t > K.WINDOW do
        rec.hist_n = rec.hist_n - 1
    end
end

function Model.jitter(rec, center)
    local lo, hi = 180, -180
    for i = 1, rec.hist_n do
        local d = U.wrap(Model.at(rec, i).yaw - center)
        lo, hi = min(lo, d), max(hi, d)
    end
    if hi - lo < K.JITTER_STEP then return nil end
    for _ = 1, 4 do
        local split, left, right, nl, nr = (lo + hi) * 0.5, 0, 0, 0, 0
        for i = 1, rec.hist_n do
            local d = U.wrap(Model.at(rec, i).yaw - center)
            if d < split then left, nl = left + d, nl + 1
            else right, nr = right + d, nr + 1 end
        end
        if nl == 0 or nr == 0 then return nil end
        lo, hi = left / nl, right / nr
    end
    local split, half = (lo + hi) * 0.5, (hi - lo) * 0.5
    if half < 6 or half > 90 then return nil end
    local prev, start, n, total, sq, residual = nil, nil, 0, 0, 0, 0
    for i = 1, rec.hist_n do
        local a = Model.at(rec, i)
        local d = U.wrap(a.yaw - center)
        local side = d < split and -1 or 1
        residual = residual + abs(d - (side == -1 and lo or hi))
        if prev and prev ~= side then
            if start then
                local duration = a.t - start
                n, total, sq = n + 1, total + duration, sq + duration * duration
            end
            start = a.t
        end
        prev = side
    end
    if n < 2 then return nil end
    local period = total / n
    if period <= 0 or period > 0.125 then return nil end
    local cv = sqrt(max(0, sq / n - period * period)) / period
    local quality = U.bound(1 - cv - residual / rec.hist_n / half, 0, 1)
    return { center = U.wrap(center + split), half = half, period = period,
        elapsed = rec.hist_time - start, side = prev, quality = quality }
end

function Model.classify(rec)
    local n = rec.hist_n
    if n < 4 then return end
    local oldest, newest = Model.at(rec, 1), Model.at(rec, n)
    local duration = newest.t - oldest.t
    if duration < 3 * K.BASE_INTERVAL then return end
    local signed, total, sx, sy, huge, flips, prior = 0, 0, 0, 0, 0, 0, 0
    local prev = oldest
    for i = 2, n do
        local a = Model.at(rec, i)
        local d, weight = U.wrap(a.yaw - prev.yaw), a.t - prev.t
        sx, sy = sx + cos(rad(prev.yaw)) * weight, sy + sin(rad(prev.yaw)) * weight
        signed, total, prev = signed + d, total + abs(d), a
        if abs(d) >= K.JITTER_STEP then
            huge = huge + 1
            local side = U.sign(d)
            if prior ~= 0 and prior ~= side then flips = flips + 1 end
            prior = side
        end
    end
    local rate, spread = signed / duration, total / duration
    local center = sx * sx + sy * sy > duration * duration * 1e-6 and deg(atan2(sy, sx)) or oldest.yaw
    local name, confidence = "random", 0.4
    if abs(rate) >= K.SPIN_RATE and abs(signed) >= total * 0.86 then
        name, confidence = "spin", abs(signed) / total
    elseif flips >= 2 and flips / max(1, huge - 1) >= 0.60 and spread >= K.STATIC_RATE * 2 then
        name, confidence = "jitter", min(1, 0.4 + 0.6 * flips / max(1, huge - 1))
    elseif spread < K.STATIC_RATE then
        name, confidence = "static", 1 - spread / K.STATIC_RATE
    elseif spread < K.SWAY_RATE then
        name, confidence = "sway", 0.7
    end

    if name ~= rec.class.name then
        if rec.candidate ~= name then
            rec.candidate, rec.class_since = name, newest.t
            return
        end
        if newest.t - rec.class_since < K.SWITCH_TIME then return end
        rec.index, rec.miss_streak, rec.last_side, rec.anti, rec.next_side = 1, 0, nil, 0, nil
    end
    rec.candidate, rec.class_since = nil, nil
    local amp = 0
    for i = 1, n do amp = amp + abs(U.wrap(Model.at(rec, i).yaw - center)) end
    rec.class = { name = name, confidence = confidence, center = center, amp = amp / n,
        rate = rate, jitter = name == "jitter" and Model.jitter(rec, center) or nil }
end

function Model.side(rec)
    if rec.manual then return rec.manual end
    if rec.next_side then return rec.next_side end
    if CFG.mode == E.BRUTE or CFG.mode == E.STATIC or CFG.mode == E.OFFSET then return rec.side end
    local m = rec.classes[rec.class.name]
    local learned = rec.side * rec.conf
    local limit = rec.conf * 0.5
    local score = learned + (CFG.cls_mem and m and U.bound(m.side * m.conf * 0.5, -limit, limit) or 0)
    for i = 1, #HINTS do
        if CFG[HINTS[i]] then score = score + rec.hints[i] * WEIGHTS[i] * RES.weights[i] * RES.signs[i] end
    end
    if abs(score) >= 0.15 then return U.sign(score) end
    return rec.pred_side or rec.side
end

function Model.pitch(rec)
    if CFG.pitch == 1 then return rec.raw.x end
    if CFG.pitch == 4 or (CFG.pitch == 3 and rec.pitch_flick >= 0.65) then return 89 end
    if CFG.pitch == 5 then return 0 end
    if CFG.pitch == 6 then return -89 end
    return U.bound(rec.raw.x, -89, 89)
end

function Model.solve(rec, index, side)
    local m, raw, at = rec.class, rec.raw.y, rec.at_target
    local base, seq, scale, effective = raw, BRUTE, CFG.desync, nil
    local adaptive = CFG.mode == E.ADAPTIVE or CFG.mode == E.JITSPIN
    local j = m.jitter
    if CFG.mode == E.OFFSET then
        base, seq, scale = at + CFG.yaw_off, SINGLE_ZERO, 0
    elseif adaptive and m.name == "jitter" and CFG.jit_mode == E.FOLLOW then
        seq, scale = SINGLE_ZERO, 0
    elseif adaptive and CFG.base == E.AUTO and j and j.quality >= 0.6 then
        local half_tick = rec.sample_interval * 0.5
        local predicted = (j.elapsed + half_tick >= j.period) and -j.side or j.side
        base, seq, scale = j.center, JITTER[CFG.jit_mode], j.half * predicted * side
    else
        if CFG.base == E.TARGET then base = at
        elseif CFG.base == E.AUTO then
            if m.name == "spin" then
                base = CFG.mode == E.JITSPIN and raw + m.rate * K.BASE_INTERVAL * 0.5 or at
            elseif m.name ~= "static" and m.center then base = m.center end
        end
        if CFG.mode == E.STATIC then seq = SINGLE_FULL
        elseif CFG.brute_pat == E.STEP then seq, scale = STEPS, CFG.brute_step end
        if m.name == "jitter" then scale = scale * CFG.jit_sc / 100
        elseif m.name == "random" then scale = scale * 0.75 end
        if rec.speed > 4 then scale = scale * CFG.move_sc / 100 end
        if CFG.face_damp and (m.name == "static" or m.name == "sway") and abs(U.wrap(raw - at)) < 35 then
            scale = scale * 0.3
        end
        scale = scale * side
        local product = seq[(index - 1) % #seq + 1] * scale
        if abs(product) >= K.CMD_MIN then effective = U.sign(product) end
    end
    local pos = (index - 1) % #seq + 1
    local yaw = U.wrap(base + scale * seq[pos])
    local delta = U.wrap(yaw - raw)
    return { yaw = yaw, pitch = Model.pitch(rec), offset = delta, side = effective,
        key = m.name .. ":" .. U.round(delta * 0.5), pos = pos, size = #seq }
end

function Model.refresh(rec)
    rec.pred_side = Model.side(rec)
    rec.correction = Model.solve(rec, rec.index, rec.pred_side)
end

function Model.advance(rec, shot, now)
    if rec.index ~= shot.index or rec.class.name ~= shot.class then return end
    local tried = rec.tried
    for i = #tried, 1, -1 do
        if U.age(tried[i].at, now) >= K.TRIED_TTL or tried[i].key == shot.key then remove(tried, i) end
    end
    if #tried == K.TRIED_MAX then remove(tried, 1) end
    tried[#tried + 1] = { key = shot.key, at = now }
    local side = Model.side(rec)
    local n = Model.solve(rec, rec.index, side).size
    local next_index = rec.index % n + 1
    if CFG.brute_skip then
        for step = 1, n do
            local ix = (rec.index + step - 1) % n + 1
            local key, seen = Model.solve(rec, ix, side).key, false
            for i = 1, #tried do if tried[i].key == key then seen = true break end end
            if not seen then next_index = ix break end
        end
    end
    rec.index = next_index
    Model.refresh(rec)
end

-- Optional schema access. Failed probes are retried; one pawn cannot disable the whole channel.
Schema.offsets = {}
local BODY_CLASSES = { "C_BaseEntity", "C_BaseModelEntity" }
local EYE_CLASSES = { "C_CSPlayerPawn", "C_CSPlayerPawnBase", "CCSPlayerPawn" }
local NODE_ANGLES = { "m_angAbsRotation", "m_angRotation" }

function Schema.offset(class, field)
    if not class or not schema then return nil end
    local key = class .. "::" .. field
    local old = Schema.offsets[key]
    if old and (old.offset or U.age(old.at, S.rt) < K.RETRY) then return old.offset end
    local offset = U.safe(schema.offset, class, field)
    if not U.int(offset) or offset <= 0 or offset >= 1048576 then offset = nil end
    Schema.offsets[key] = { offset = offset, at = S.rt }
    return offset
end

function Schema.get(pawn, class, field, kind)
    local offset = Schema.offset(class, field)
    if offset then return U.call(pawn, "get", offset, kind) end
end

function Schema.simtime(pawn, rec)
    local t = Schema.get(pawn, rec.native_class, "m_flSimulationTime", "float")
    if t == nil then t = Schema.get(pawn, "C_BaseEntity", "m_flSimulationTime", "float") end
    if U.finite(t) and t > 0 then return t end
end

function Schema.insecure()
    return client and U.safe(client.insecure) == true
end

function Schema.angles_equal(a, b, eps)
    return U.yaw_equal(a, b, eps) and abs(U.wrap(a.z - b.z)) <= eps
end

function Schema.node_yaw(pawn, rec)
    if not CFG.scene_hint or not S.insecure or not memory then return nil end
    if U.age(rec.node_failed, S.rt) < 0.7 then return nil end
    local node
    for i = 1, #BODY_CLASSES do
        local body = Schema.get(pawn, BODY_CLASSES[i], "m_CBodyComponent", "ptr")
        if U.ptr(body) then
            local offset = Schema.offset("CBodyComponent", "m_pSceneNode")
            if offset then node = U.safe(memory.read, "ptr", body + offset) end
            if not U.ptr(node) then
                offset = Schema.offset("CBodyComponent", "m_pBodySceneNode")
                if offset then node = U.safe(memory.read, "ptr", body + offset) end
            end
            if U.ptr(node) then break end
        end
    end
    if not U.ptr(node) then
        node = Schema.get(pawn, "C_BaseEntity", "m_pGameSceneNode", "ptr")
    end
    if U.ptr(node) then
        for _, field in ipairs(NODE_ANGLES) do
            local offset = Schema.offset("CGameSceneNode", field)
            local angles = offset and U.safe(memory.read, "vector", node + offset)
            if U.vec(angles) and abs(angles.y) <= 360 and abs(U.wrap(angles.y - rec.raw.y)) <= 110 then
                return angles.y
            end
        end
    end
    rec.node_failed = S.rt
    return nil
end

function Schema.release(pawn, rec)
    local write = rec.mem
    if not write then return true end
    if not Schema.insecure() then return false end
    local current = U.call(pawn, "get", write.offset, "vector")
    if not U.vec(current) then return false end
    if Schema.angles_equal(current, write.angles, 0.02) then
        local ok, value = pcall(invoke, pawn, "set", write.offset, "vector", write.before)
        if not ok or value == false or not Schema.angles_equal(U.call(pawn, "get", write.offset, "vector"), write.before, 0.02) then
            U.report("eye-angle restore", "could not verify restoration")
            return false
        end
    end
    rec.mem = nil
    return true
end

function Schema.apply(pawn, rec)
    if not CFG.mem_write or not S.insecure or not rec.correction then return end
    if S.menu and CFG.pause_menu then return end
    if U.age(S.last_move, S.rt) > K.WATCHDOG then return end
    if not Schema.insecure() or U.age(rec.write_failed, S.rt) < 1 then return end
    if rec.mem and not Schema.release(pawn, rec) then return end
    local offset, before
    for i = 0, #EYE_CLASSES do
        local class = i == 0 and rec.native_class or EYE_CLASSES[i]
        local candidate = Schema.offset(class, "m_angEyeAngles")
        local value = candidate and U.call(pawn, "get", candidate, "vector")
        if Schema.angles_equal(value, rec.raw, 0.06) and abs(value.z) <= 180 then
            offset, before = candidate, value
            break
        end
    end
    if offset then
        local solved = rec.correction
        local angles = vector(solved.pitch, solved.yaw, before.z)
        if Schema.angles_equal(before, angles, 0.02) then return end
        -- A read-back proves the client field changed, not that the animation graph rebuilt.
        local ok, result = pcall(invoke, pawn, "set", offset, "vector", angles)
        local readback = U.call(pawn, "get", offset, "vector")
        if Schema.angles_equal(readback, angles, 0.02) then
            rec.mem = { offset = offset, angles = angles, before = before, verified = ok and result ~= false, at = S.rt }
            if rec.mem.verified then return end
            Schema.release(pawn, rec)
        elseif not U.vec(readback) then
            rec.mem = { offset = offset, angles = angles, before = before, verified = false }
        end
    end
    rec.write_failed = S.rt
    U.report("eye-angle write", "unavailable or unverified; command channel remains eligible")
end

function Schema.delivered(pawn, rec)
    local w = rec.mem
    return CFG.mem_write and w and w.verified and U.age(w.at, S.rt) <= K.STALE and Schema.insecure()
        and Schema.angles_equal(U.call(pawn, "get", w.offset, "vector"), w.angles, 0.02)
end

-- Hitbox indices are scoped to a pawn life. Bone indices come from the hitbox metadata.
local HITBOX_GROUPS = { [1] = "head", [2] = "chest", [3] = "stomach", [4] = "la", [5] = "ra", [6] = "ll", [7] = "rl" }

function HB.indices(pawn, rec)
    if rec.boxes and U.age(rec.boxes.at, S.rt) < K.HB_TTL then return rec.boxes end
    local out = { at = S.rt }
    local boxes = U.call(pawn, "hitboxes")
    if type(boxes) == "table" then
        for i = 1, min(#boxes, 96) do
            local h = boxes[i]
            local group = type(h) == "table" and HITBOX_GROUPS[h.group]
            if group and U.int(h.index) and h.index >= 0 then
                local height = U.vec(h.center) and h.center.z or -math.huge
                if not out[group] or out[group].height < height then
                    out[group] = { index = h.index, bone = h.bone, height = height }
                end
            end
        end
    end
    rec.boxes = out
    return out
end

function HB.point(pawn, entry, head)
    local p = entry and U.call(pawn, "hitbox", entry.index)
    if not U.vec(p) and entry and U.int(entry.bone) and entry.bone >= 0 then
        p = U.call(pawn, "bone", entry.bone)
    end
    if not U.vec(p) and head then p = U.call(pawn, "bone", 6) end
    if U.vec(p) then return p end
end

function HB.body_yaw(pawn, rec)
    local boxes = HB.indices(pawn, rec)
    for i = 1, 2 do
        local lk, rk = "ll", "rl"
        if i == 2 then lk, rk = "la", "ra" end
        local left, right = HB.point(pawn, boxes[lk]), HB.point(pawn, boxes[rk])
        if left and right then
            local x, y = left.x - right.x, left.y - right.y
            if x * x + y * y >= 4 then
                local yaw = U.wrap(deg(atan2(y, x)) - 90)
                if abs(U.wrap(yaw - rec.raw.y)) <= 110 then return yaw end
            end
        end
    end
end

function Store.limit(data)
    local list = {}
    for k, entry in pairs(data) do list[#list + 1] = { k = k, t = entry.t } end
    if #list > K.DB_MAX then
        sort(list, function(a, b) return a.t > b.t or (a.t == b.t and a.k < b.k) end)
        for i = K.DB_MAX + 1, #list do data[list[i].k] = nil end
    end
end

function Store.load()
    Store.data, Store.dirty, Store.clearing, Store.last_save, Store.count = {}, false, false, nil, 0
    local data = db and U.safe(db.load, META.learned, {})
    if type(data) ~= "table" then return end
    for key, row in pairs(data) do
        if type(key) == "string" and #key <= 20 and key:match("^[1-9]%d*$") and type(row) == "table" then
            local conf, time = tonumber(row.conf), tonumber(row.t)
            local hits, misses = tonumber(row.hits), tonumber(row.misses)
            Store.data[key] = { side = row.side == -1 and -1 or 1,
                conf = U.finite(conf) and U.bound(conf, 0, 1) or 0,
                t = U.finite(time) and time or 0,
                hits = U.finite(hits) and floor(U.bound(hits, 0, 1000000)) or 0,
                misses = U.finite(misses) and floor(U.bound(misses, 0, 1000000)) or 0 }
        end
    end
    Store.limit(Store.data)
    for _ in pairs(Store.data) do Store.count = Store.count + 1 end
end

function Store.remember(rec)
    if not CFG.persist or not rec.sid then return end
    if not Store.data[rec.sid] then Store.count = Store.count + 1 end
    Store.data[rec.sid] = { side = rec.side, conf = rec.conf, t = os.time(), hits = rec.hits, misses = rec.misses }
    Store.dirty = true
    if Store.count > K.DB_MAX then
        Store.limit(Store.data)
        Store.count = K.DB_MAX
    end
end

function Store.flush(force)
    if not Store.dirty or not (CFG.persist or Store.clearing) then return true end
    if not force and U.age(Store.last_save, S.rt) < K.RETRY then return false end
    Store.last_save = S.rt
    if db and U.safe(db.save, META.learned, Store.data) == true then
        Store.dirty, Store.clearing = false, false
        return true
    end
    U.report("learning database", "write failed; changes retained for retry")
    return false
end

function RES.identity(controller, pawn)
    local sid = U.call(controller, "steam_id") or U.call(pawn, "steam_id")
    if type(sid) == "string" and #sid <= 20 and sid:match("^[1-9]%d*$") then return sid, sid end
    local a = U.addr(controller)
    if a then return "c" .. format("%.0f", a) end
    a = U.addr(pawn)
    if a then return "p" .. format("%.0f", a) end
end

function RES.invalidate(rec)
    if rec.addr and RES.by_addr[rec.addr] == rec then RES.by_addr[rec.addr] = nil end
    rec.addr, rec.mem, rec.boxes, rec.eye, rec.origin = nil, nil, nil, nil, nil
    rec.reveal, rec.lc, rec.sim, rec.tick, rec.hint_at = nil, nil, nil, nil, nil
    rec.reset_history = nil
    rec.move_at, rec.move_yaw, rec.applied_at = nil, nil, nil
    rec.node_failed, rec.write_failed, rec.delivery = nil, nil, nil
    rec.manual, rec.pred_side, rec.next_side, rec.last_side = nil, nil, nil, nil
    rec.index, rec.anti, rec.hit_streak, rec.miss_streak = 1, 0, 0, 0
    rec.tried, rec.hints = {}, { 0, 0, 0, 0 }
    Model.reset(rec)
end

function RES.bind(row, addr)
    local key, sid = RES.identity(row.controller, row.pawn)
    if not key then return nil end
    local rec = RES.records[key]
    if not rec then
        local saved = sid and CFG.persist and Store.data[sid]
        rec = { key = key, sid = sid, history = {}, classes = {},
            side = saved and saved.side or 1, conf = saved and min(0.6, saved.conf * 0.6) or 0.3,
            hits = saved and saved.hits or 0, misses = saved and saved.misses or 0 }
        RES.records[key] = rec
    end
    local collision = RES.by_addr[addr]
    if collision and collision ~= rec then RES.invalidate(collision) end
    if rec.addr ~= addr then
        RES.invalidate(rec)
        RES.serial = RES.serial + 1
        rec.life, rec.addr = RES.serial, addr
        rec.native_class = U.call(row.pawn, "class_name")
        if type(rec.native_class) ~= "string" then rec.native_class = nil end
        rec.name = U.call(row.controller, "name") or U.call(row.pawn, "name") or "Player"
        if type(rec.name) ~= "string" then rec.name = "Player" end
    end
    RES.by_addr[addr] = rec
    return rec
end

function RES.present(rec, age)
    return rec and rec.addr and rec.eye and RES.by_addr[rec.addr] == rec
        and U.age(rec.seen, S.rt) <= (age or K.STALE)
end

function RES.ready(rec)
    return RES.present(rec) and rec.raw and rec.correction and U.age(rec.sample_rt, S.rt) <= K.STALE
        and U.age(rec.lc, S.rt) >= K.LC_HOLD and U.age(rec.reveal, S.rt) >= K.REVEAL
end

function RES.cover(from, to, local_pawn, pawn)
    local yaw = rad(U.yaw(from, to))
    local x, y = sin(yaw) * 26, -cos(yaw) * 26
    local opts = { skip = { local_pawn, pawn }, mask = trace.mask and trace.mask.visible }
    local l = U.safe(trace.line, from, vector(to.x - x, to.y - y, to.z), opts)
    local r = U.safe(trace.line, from, vector(to.x + x, to.y + y, to.z), opts)
    if type(l) ~= "table" or type(r) ~= "table" or not U.finite(l.fraction) or not U.finite(r.fraction) then return 0 end
    return U.bound((l.fraction - r.fraction) * 2, -1, 1)
end

function RES.hints(pawn, me, eye, rec)
    local yaw, h = rec.raw.y, rec.hints
    if U.age(rec.hint_at, S.rt) >= K.HINT_EVERY then
        rec.hint_at = S.rt
        local body = CFG.body and (Schema.node_yaw(pawn, rec) or HB.body_yaw(pawn, rec))
        local d = body and U.wrap(body - yaw) or 0
        h[1] = abs(d) >= 8 and abs(d) <= 110 and U.bound(d / 35, -1, 1) or 0
        h[2] = CFG.freestand and RES.cover(eye, rec.eye, me, pawn) or 0
    end
    local age = U.age(rec.move_at, S.rt)
    local d = rec.move_yaw and U.wrap(rec.move_yaw - yaw) or 0
    h[3] = rec.speed <= 4 and age < 1 and abs(d) >= 20 and U.sign(d) * (1 - max(0, age)) or 0
    h[4] = rec.speed > 45 and rec.move_yaw and U.sign(U.wrap(rec.move_yaw - rec.at_target)) or 0
end

function RES.sample(rec, pawn, me, from, tick, interval)
    local origin, eye = U.call(pawn, "origin"), U.call(pawn, "eye_position")
    local clean = not rec.mem or Schema.release(pawn, rec)
    if not U.vec(origin) or not U.vec(eye) then
        rec.eye, rec.origin, rec.correction, rec.sample_rt = nil, nil, nil, nil
        return
    end
    local old_origin = rec.origin
    rec.origin, rec.eye, rec.seen = origin, eye, S.rt
    -- Do not feed a possibly still active local write back into the network history.
    if not clean or not CFG.enable or not U.vec(from) then rec.correction = nil return end
    local angles, vel = U.call(pawn, "eye_angles"), U.call(pawn, "velocity")
    if not U.vec(angles) or not U.vec(vel) then
        rec.correction, rec.sample_rt = nil, nil
        return
    end
    local sim = Schema.simtime(pawn, rec)
    local step = rec.tick and (tick - rec.tick) * interval or interval
    local unchanged = tick == rec.tick
    if sim and rec.sim then
        step = sim - rec.sim
        unchanged = abs(step) < 0.00001
    end
    local teleported = false
    if old_origin then
        local x, y, z = origin.x - old_origin.x, origin.y - old_origin.y, origin.z - old_origin.z
        teleported = x * x + y * y + z * z > 4096
    end
    if unchanged and not teleported and rec.sample_rt then return end
    rec.sim, rec.tick = sim, tick
    if step < -0.00001 or teleported then
        rec.reset_history = true
        if CFG.lc_detect then rec.lc = S.rt end
    end
    local frozen = U.age(rec.lc, S.rt) < K.LC_HOLD
    if (CFG.lc_hold and frozen) or U.age(rec.reveal, S.rt) < K.REVEAL then return end
    local dt = rec.sample_tick and (tick - rec.sample_tick) * interval or interval
    if rec.sample_sim and sim then dt = sim - rec.sample_sim end
    if dt > K.STALE or dt <= 0 or rec.reset_history or U.age(rec.sample_rt, S.rt) > K.STALE then
        Model.reset(rec)
        rec.reset_history = nil
        dt = interval
    end
    rec.sample_interval = U.bound(dt, interval * 0.5, K.STALE)
    rec.raw = vector(angles.x, U.wrap(angles.y), angles.z)
    rec.speed = sqrt(vel.x * vel.x + vel.y * vel.y)
    rec.at_target = U.yaw(eye, from)
    if rec.speed > 4 then rec.move_yaw, rec.move_at = deg(atan2(vel.y, vel.x)), S.rt end
    Model.push(rec, rec.raw.y, rec.raw.x, rec.sample_interval)
    Model.classify(rec)
    rec.sample_rt, rec.sample_tick, rec.sample_sim = S.rt, tick, sim
    RES.hints(pawn, me, from, rec)
    if rec.hist_n >= 4 then
        Model.refresh(rec)
        if not frozen then Schema.apply(pawn, rec) end
    end
end

function RES.frame()
    if not S.active or (not CFG.enable and not CFG.rb_enable) then return end
    local tick = U.safe(globals.tickcount)
    if not U.int(tick) or tick == RES.frame_tick then return end
    RES.frame_tick = tick
    local me = U.safe(entity.local_pawn)
    local from = U.call(me, "alive") == true and U.call(me, "eye_position") or nil
    local players = U.safe(entity.players)
    if type(players) ~= "table" then return end
    local interval = U.interval()
    S.insecure = Schema.insecure()
    for _, row in ipairs(players) do
        local pawn = type(row) == "table" and row.pawn or nil
        if U.call(pawn, "is_enemy") == true and U.call(pawn, "alive") == true then
            local addr = U.addr(pawn)
            local rec = addr and RES.bind(row, addr)
            if rec then U.guard("resolver sample", RES.sample, rec, pawn, me, from, tick, interval) end
        end
    end
    for _, rec in pairs(RES.by_addr) do
        if U.age(rec.seen, S.rt) > K.LINGER then RES.invalidate(rec) end
    end
end

function RES.release_all()
    local players = U.safe(entity.players)
    if type(players) ~= "table" then return end
    for _, row in ipairs(players) do
        local a = type(row) == "table" and U.addr(row.pawn)
        local record = a and RES.by_addr[a]
        if record and record.mem and record.key == RES.identity(row.controller, row.pawn) then
            U.guard("memory cleanup", Schema.release, row.pawn, record)
        end
    end
end

function RES.clear(forget, round)
    RES.release_all()
    for _, rec in pairs(RES.records) do
        if round then
            rec.conf = rec.conf * 0.85
            for _, m in pairs(rec.classes) do m.conf = m.conf * 0.85 end
        end
        RES.invalidate(rec)
    end
    if forget then RES.records = {} end
    RES.by_addr, RES.frame_tick = {}, nil
end

function RES.purge()
    if U.age(RES.purge_at, S.rt) < K.PURGE_EVERY then return end
    RES.purge_at = S.rt
    local idle, n = {}, 0
    for key, rec in pairs(RES.records) do
        if rec.addr and U.age(rec.seen, S.rt) > K.LINGER then RES.invalidate(rec) end
        if not rec.addr and U.age(rec.seen, S.rt) >= K.PURGE_AGE then RES.records[key] = nil
        else
            n = n + 1
            if not rec.addr then idle[#idle + 1] = rec end
        end
    end
    if n > K.RECORD_MAX then
        sort(idle, function(a, b) return (a.seen or -1) < (b.seen or -1) end)
        for i = 1, min(#idle, n - K.RECORD_MAX) do RES.records[idle[i].key] = nil end
    end
end

function RES.from_event(ev, name)
    local pawn = U.call(ev, "get_pawn", name)
    local controller = U.call(ev, "get_controller", name)
    local key = RES.identity(controller, pawn)
    local addr = U.addr(pawn)
    local rec = addr and RES.by_addr[addr] or (key and RES.records[key])
    if rec and rec.addr and (not addr or rec.addr == addr) and (not controller or rec.key == key) then return rec end
end

function RES.init()
    RES.by_addr, RES.records, RES.serial = {}, {}, 0
    RES.weights, RES.signs, RES.flipped = { 1, 1, 1, 1 }, { 1, 1, 1, 1 }, {}
end

-- A command and its subticks are inspected and mutated only within createmove.
local SUB_FIELDS = { when = true, button = true, pressed = true, forward = true, left = true,
    pitch = true, yaw = true, index = true, is_button = true }

function CMD.read_attack(cmd, view)
    local steps = U.call(cmd, "subticks")
    if type(steps) ~= "table" then return nil end
    local attack, release, index = buttons.attack, false, nil
    local yaw, pitch = 0, 0
    local when = -1
    for i = 1, #steps do
        local s = steps[i]
        if type(s) ~= "table" then return nil end
        if not U.finite(s.when) or s.when < when or s.when < 0 or s.when > 1 then return nil end
        when = s.when
        if not (s.pitch == nil or U.finite(s.pitch)) or not (s.yaw == nil or U.finite(s.yaw)) then return nil end
        if not index then yaw, pitch = yaw + (s.yaw or 0), pitch + (s.pitch or 0) end
        if s.is_button ~= false and U.int(s.button) and bit.band(s.button, attack) ~= 0 then
            if s.pressed == true then
                if index or s.button ~= attack then return nil end
                index = i
            else
                release = true
            end
        end
    end
    if index then
        return { index = index, steps = steps, view = vector(view.x + pitch, U.wrap(view.y + yaw), 0) }
    elseif not release and U.call(cmd, "has", attack) == true then
        return { view = view }
    end
end

function CMD.serialize(steps)
    local out = {}
    for i = 1, #steps do
        local s = steps[i]
        for key in pairs(s) do if not SUB_FIELDS[key] then return nil end end
        if not U.finite(s.when) or s.when < 0 or s.when > 1 then return nil end
        if (s.pitch or 0) ~= 0 then return nil end -- Legacy add_subtick has no pitch parameter.
        if s.button ~= nil and (not U.int(s.button) or s.button < 0) then return nil end
        if s.pressed ~= nil and type(s.pressed) ~= "boolean" then return nil end
        if s.is_button == false and (s.button or 0) ~= 0 then return nil end
        if s.is_button == true and ((s.button or 0) == 0 or s.pressed == nil) then return nil end
        if s.forward ~= nil and not U.finite(s.forward) then return nil end
        if s.left ~= nil and not U.finite(s.left) then return nil end
        out[i] = { when = s.when, button = s.button, pressed = s.pressed, yaw = s.yaw, left = s.left, forward = s.forward }
    end
    return out
end

function CMD.same_steps(got, expect)
    if type(got) ~= "table" or #got ~= #expect then return false end
    for i = 1, #expect do
        local a, b = got[i], expect[i]
        if type(a) ~= "table" or not U.same(a.when, b.when) or (a.button or 0) ~= (b.button or 0)
            or (a.pressed == true) ~= (b.pressed == true) or (a.pitch or 0) ~= 0
            or not U.same(a.yaw or 0, b.yaw or 0) or not U.same(a.left or 0, b.left or 0)
            or not U.same(a.forward or 0, b.forward or 0) then return false end
        if (b.button or 0) ~= 0 and (a.is_button == false or a.pressed ~= b.pressed) then return false end
    end
    return true
end

function CMD.replace_steps(cmd, steps)
    local ok, result = pcall(invoke, cmd, "clear_subticks")
    if not ok or result == false then return false end
    for i = 1, #steps do
        if U.call(cmd, "add_subtick", steps[i]) ~= true then return false end
    end
    return CMD.same_steps(U.call(cmd, "subticks"), steps)
end

function CMD.lock(cmd)
    local ok, result = pcall(invoke, cmd, "lock_angles")
    return ok and result ~= false
end

function CMD.subtick_fix(cmd, attack, angles)
    if abs(angles.x - attack.view.x) > 0.025 then return false end
    local before = CMD.serialize(attack.steps)
    if not before then return false end
    local after = U.copy(before)
    local step = U.copy(after[attack.index])
    step.yaw = (step.yaw or 0) + U.wrap(angles.y - attack.view.y)
    after[attack.index] = step
    if CMD.replace_steps(cmd, after) and CMD.lock(cmd) then return true end
    if not CMD.replace_steps(cmd, before) then
        CMD.failed = true
        U.report("subtick rollback", "restore failed; command edits suspended until map change")
    else
        U.report("subtick writer", "round-trip rejected; original steps restored")
    end
    return false
end

function CMD.observe_move(cmd)
    local ok, f, s = pcall(invoke, cmd, "move")
    if not ok or not U.finite(f) or not U.finite(s) then return nil end
    local l, r = U.call(cmd, "has", buttons.left) == true, U.call(cmd, "has", buttons.right) == true
    if l ~= r and abs(s) > 0.01 then
        local axis = U.sign(s) * (l and 1 or -1)
        if CMD.last_axis ~= axis then CMD.last_axis, CMD.axis_count, CMD.axis = axis, 0, nil end
        CMD.axis_count = CMD.axis_count + 1
        if CMD.axis_count >= 2 then CMD.axis, CMD.axis_count = axis, 2 end
    end
    return f, s
end

function CMD.base_fix(cmd, raw, angles, forward, side)
    local f, s = forward, side
    local adjust = CFG.rotate_move and U.finite(f) and U.finite(s) and abs(f) + abs(s) > 0.001
    if CFG.rotate_move and not U.finite(f) then return false end
    if adjust then
        local axis = CMD.axis
        if not axis then return false end
        local d = rad(U.wrap(angles.y - raw.y))
        local c, v = cos(d), sin(d)
        f, s = f * c + axis * s * v, s * c - axis * f * v
        local size = max(abs(f), abs(s))
        if max(abs(forward), abs(side)) <= 1 and size > 1 then f, s = f / size, s / size end
    end
    local ok, result = pcall(invoke, cmd, "set_view_angles", vector(angles.x, angles.y, raw.z))
    local success = ok and result ~= false and U.yaw_equal(U.call(cmd, "view_angles"), angles, 0.02)
    if success and adjust then
        ok, result = pcall(invoke, cmd, "set_move", f, s)
        local read, ff, ss = pcall(invoke, cmd, "move")
        success = ok and result ~= false and read and U.same(ff, f) and U.same(ss, s)
    end
    if success and CMD.lock(cmd) then return true end
    pcall(invoke, cmd, "set_view_angles", raw)
    if adjust then pcall(invoke, cmd, "set_move", forward, side) end
    local read, ff, ss = pcall(invoke, cmd, "move")
    if not U.yaw_equal(U.call(cmd, "view_angles"), raw, 0.02)
        or (adjust and (not read or not U.same(ff, forward) or not U.same(ss, side))) then
        CMD.failed = true
        U.report("command rollback", "restore failed; command edits suspended until map change")
    else
        U.report("angle writer", "native command edit or lock was rejected")
    end
    return false
end

function CMD.probe(attack, from)
    local v = attack.view
    if not U.vec(v) or abs(v.x) > 89.1 then return nil end
    local ray = U.safe(trace.bullet, from, from + v:forward() * K.RAY_LENGTH)
    if type(ray) ~= "table" or ray.hit ~= true or not ray.entity or not U.vec(ray.position) then return nil end
    local pawn = ray.entity
    local a = U.addr(pawn)
    local rec = a and RES.by_addr[a]
    if not RES.present(rec) or U.call(pawn, "alive") ~= true or U.call(pawn, "is_enemy") ~= true then return nil end
    local sid = U.call(pawn, "steam_id")
    if rec.sid and type(sid) == "string" and sid ~= "0" and sid ~= rec.sid then return nil end
    return rec, ray
end

function CMD.fix(cmd, attack, from, rec, ray, f, s)
    if not RES.ready(rec) then return nil end
    local pawn = ray.entity
    if Schema.delivered(pawn, rec) then return "memory" end
    if not CFG.cmd_fix or CMD.failed then return nil end
    local eye = U.call(pawn, "eye_angles")
    if not U.yaw_equal(eye, rec.raw, 1) then return nil end
    local solution = rec.correction
    local delta = U.wrap(solution.yaw - eye.y)
    if abs(delta) < K.CMD_MIN or abs(delta) > K.CMD_MAX then return nil end
    local pivot = U.call(pawn, "origin")
    if not U.vec(pivot) then return nil end
    local a, b = ray.position.x - pivot.x, ray.position.y - pivot.y
    local r = rad(delta)
    local dest = vector(pivot.x + a * cos(r) - b * sin(r), pivot.y + a * sin(r) + b * cos(r), ray.position.z)
    local angle = U.safe(math.calc_angle, from, dest)
    if not U.vec(angle) or abs(angle.x) > 89 or U.yaw_equal(angle, attack.view, 0.025) then return nil end
    local applied, channel
    if attack.index then
        applied, channel = CMD.subtick_fix(cmd, attack, angle), "subtick"
    else
        applied, channel = CMD.base_fix(cmd, attack.view, angle, f, s), "command"
    end
    if applied then
        rec.applied_at, rec.delivery = S.rt, channel
        return channel
    end
end

-- Only weapon_fire creates a shot. A command intent cannot be consumed twice.
function Feedback.finish(shot, result)
    if not shot.key or shot.result then return false end
    shot.result = result
    Feedback.stats[result] = Feedback.stats[result] + 1
    return true
end

function Feedback.clear(reset_stats)
    if not reset_stats and Feedback.fires then
        for i = 1, #Feedback.fires do Feedback.finish(Feedback.fires[i], "void") end
    end
    Feedback.intents, Feedback.fires = {}, {}
    if reset_stats then Feedback.stats = { fired = 0, tracked = 0, hit = 0, miss = 0, void = 0, unpaired = 0 } end
end

function Feedback.intent(info, rec, ray, channel, air, from)
    local name = U.weapon_name(info.name)
    if not name or not CFG.feedback then return end
    local solved = rec and rec.correction
    local entry = { weapon = name, t = S.rt, epoch = S.epoch }
    if rec and RES.present(rec) then
        entry.key, entry.life, entry.class, entry.index = rec.key, rec.life, rec.class.name, rec.index
        entry.channel, entry.air, entry.moving = channel, air, (rec.speed or 0) > 40
        entry.lc = U.age(rec.lc, S.rt) < K.LC_HOLD
        entry.side, entry.offset = solved and solved.side, solved and solved.key
        entry.head = RB.target == rec and RB.head == true
        local p = ray.penetrated
        entry.direct = p == false or p == 0
        local ia, sp = info.inaccuracy, info.spread
        if U.finite(ia) and U.finite(sp) and ia >= 0 and sp >= 0 and ia + sp < 1 then
            local x, y, z = ray.position.x - from.x, ray.position.y - from.y, ray.position.z - from.z
            entry.cone = sqrt(x * x + y * y + z * z) * (ia + sp)
        end
        entry.hints, entry.signs = {}, {}
        for i = 1, #HINTS do
            entry.signs[i] = RES.signs[i]
            entry.hints[i] = CFG[HINTS[i]] and U.sign(rec.hints[i]) * RES.signs[i] or 0
        end
    end
    local queue = Feedback.intents
    if #queue == K.INTENT_MAX then remove(queue, 1) end
    queue[#queue + 1] = entry
end

function Feedback.local_event(ev, field)
    return U.you(U.call(ev, "get_pawn", field), "local_pawn")
        or U.you(U.call(ev, "get_controller", field), "local_controller")
end

function Feedback.weapon_fire(ev)
    if not S.active or not CFG.enable then return end
    if not Feedback.local_event(ev, "userid") then
        local rec = RES.from_event(ev, "userid")
        if rec then rec.reveal = S.rt end
        return
    end
    if not CFG.feedback then return end
    local name = U.weapon_name(U.call(ev, "get_string", "weapon"))
    if not name then return end
    local matched, queue = nil, Feedback.intents
    for i = #queue, 1, -1 do
        local item = queue[i]
        local age = U.age(item.t, S.rt)
        if item.epoch ~= S.epoch or age > K.INTENT_AGE then remove(queue, i)
        elseif not matched and item.weapon == name then
            matched = remove(queue, i)
            -- The event has no command number. Conflicting recent intents are not evidence.
            for j = i - 1, 1, -1 do
                local older = queue[j]
                if older.weapon == name then
                    if older.epoch == S.epoch and U.age(older.t, S.rt) <= K.INTENT_AGE then
                        if older.key ~= matched.key or older.life ~= matched.life then matched.key = nil
                        elseif older.offset ~= matched.offset or older.channel ~= matched.channel then matched.ambiguous = true end
                    end
                    remove(queue, j)
                end
            end
            break
        end
    end
    if not matched then
        local current = U.weapon(U.safe(entity.local_pawn))
        if not current or U.weapon_name(current.name) ~= name then return end
    end
    local shot = matched or { weapon = name, epoch = S.epoch }
    local rec = shot.key and RES.records[shot.key]
    if not RES.present(rec) or rec.life ~= shot.life then shot.key = nil end
    shot.fired, shot.window = S.rt, CFG.miss_win / 1000
    local st, queue_fires = Feedback.stats, Feedback.fires
    st.fired = st.fired + 1
    if shot.key then st.tracked = st.tracked + 1 end
    if #queue_fires == K.PENDING_MAX then Feedback.finish(remove(queue_fires, 1), "void") end
    queue_fires[#queue_fires + 1] = shot
end

function Feedback.trainable(shot)
    return shot.channel == "command" or shot.channel == "subtick"
end

function Feedback.hit(rec, shot, head, damage)
    if not Feedback.finish(shot, "hit") then return end
    rec.hits = rec.hits + 1
    if Feedback.trainable(shot) and not shot.lc and not shot.ambiguous and rec.class.name == shot.class then
        local partial = CFG.body_partial and not head and shot.head
        rec.hit_streak, rec.miss_streak = rec.hit_streak + 1, 0
        rec.conf = min(1, rec.conf + (head and 0.33 or (partial and 0.12 or 0.25)))
        if shot.side and not partial then
            rec.side, rec.index, rec.tried = shot.side, 1, {}
            local m = rec.classes[shot.class]
            rec.classes[shot.class] = { side = shot.side,
                conf = min(1, (m and m.side == shot.side and m.conf or 0) + 0.34) }
            if rec.last_side then rec.anti = U.bound(rec.anti + (rec.last_side == shot.side and -1 or 1), 0, 3) end
            rec.last_side = shot.side
            rec.next_side = CFG.anti_ab and rec.anti >= 2 and -shot.side or nil
            if CFG.hint_learn then
                for i = 1, #HINTS do
                    local h = shot.hints[i]
                    if h ~= 0 and shot.signs[i] == RES.signs[i] then
                        local w = U.bound(RES.weights[i] + (h == shot.side and 0.04 or -0.06), 0.4, 1.6)
                        if w <= 0.400001 and not RES.flipped[i] then
                            RES.flipped[i], RES.signs[i], w = true, -RES.signs[i], 1
                        end
                        RES.weights[i] = w
                    end
                end
            end
        end
        if RES.ready(rec) then Model.refresh(rec) end
        Store.remember(rec)
    end
    VIS.push(head and "HEAD" or "HIT", rec.name .. " / " .. damage)
end

function Feedback.player_hurt(ev)
    if not S.active or not CFG.enable or not CFG.feedback then return end
    if not Feedback.local_event(ev, "attacker") then
        if CFG.flip_on_hurt and Feedback.local_event(ev, "userid") then
            local attacker = RES.from_event(ev, "attacker")
            if RES.ready(attacker) then
                attacker.next_side = -(attacker.pred_side or attacker.side)
                Model.refresh(attacker)
            end
        end
        return
    end
    local name = U.weapon_name(U.call(ev, "get_string", "weapon"))
    local damage = U.call(ev, "get_int", "dmg_health")
    if not name or not U.int(damage) or damage <= 0 then return end
    local rec = RES.from_event(ev, "userid")
    local shot
    for i = #Feedback.fires, 1, -1 do
        local candidate = Feedback.fires[i]
        if candidate.weapon == name and candidate.epoch == S.epoch and U.age(candidate.fired, S.rt) <= candidate.window then
            shot = candidate
            break
        end
    end
    if shot and not shot.result and rec and shot.key == rec.key and shot.life == rec.life then
        Feedback.hit(rec, shot, U.call(ev, "get_int", "hitgroup") == K.HEAD, damage)
    else
        Feedback.stats.unpaired = Feedback.stats.unpaired + 1
        if shot and not shot.result then shot.ambiguous = true end
        if rec then
            for i = #Feedback.fires, 1, -1 do
                local other = Feedback.fires[i]
                if other.weapon == name and other.key == rec.key and other.life == rec.life and not other.result
                    and U.age(other.fired, S.rt) <= other.window then other.ambiguous = true end
            end
        end
    end
end

function Feedback.miss(shot, rec)
    if not Feedback.finish(shot, "miss") then return end
    rec.misses = rec.misses + 1
    local soft = shot.moving or shot.air or (CFG.spread_blame and (not shot.cone or shot.cone > 5))
    local credit = Feedback.trainable(shot) and shot.direct and not shot.lc and rec.class.name == shot.class
        and RES.ready(rec) and (soft and 0.5 or 1) or 0
    if credit > 0 then
        rec.last_side, rec.next_side, rec.hit_streak = nil, nil, 0
        rec.conf = max(0, rec.conf - 0.2 * credit)
        local m = rec.classes[shot.class]
        if m and m.side == shot.side then m.conf = max(0, m.conf - 0.25 * credit) end
        rec.miss_streak = rec.miss_streak + credit
        if rec.miss_streak >= CFG.miss_tol and shot.offset then
            Model.advance(rec, { index = shot.index, class = shot.class, key = shot.offset }, S.rt)
            rec.miss_streak = 0
        end
        Store.remember(rec)
    end
    VIS.push("MISS", rec.name .. (credit == 0 and " / no learning" or (soft and " / soft" or " / estimated")))
end

function Feedback.expire()
    if not CFG.enable or not CFG.feedback then
        if #Feedback.fires > 0 or #Feedback.intents > 0 then Feedback.clear(false) end
        return
    end
    local queue, i = Feedback.fires, 1
    while i <= #queue do
        local shot = queue[i]
        if U.age(shot.fired, S.rt) > shot.window then
            remove(queue, i)
            if shot.key and not shot.result then
                local rec = RES.records[shot.key]
                if not RES.present(rec) or shot.life ~= rec.life or shot.lc or shot.ambiguous then Feedback.finish(shot, "void")
                else Feedback.miss(shot, rec) end
            end
        else i = i + 1 end
    end
end

function Feedback.death(ev)
    if Feedback.local_event(ev, "userid") then
        LIFE.local_down("Local player dead")
        return
    end
    local rec = RES.from_event(ev, "userid")
    if not rec then return end
    for i = 1, #Feedback.fires do
        local shot = Feedback.fires[i]
        if shot.key == rec.key and shot.life == rec.life then Feedback.finish(shot, "void") end
    end
    RES.invalidate(rec)
end

-- Config linking accepts only real, unambiguous paths with a supported value shape.
local SLOTS = { "hc", "dmg", "safe", "baim", "hitbox" }
local KEYS = {
    hc = { hitchance = true, minimumhitchance = true },
    dmg = { mindamage = true, minimumdamage = true },
    safe = { safepoint = true, forcesafepoint = true, prefersafepoint = true },
    baim = { bodyaim = true, forcebodyaim = true, preferbodyaim = true, baim = true },
    hitbox = { hitbox = true, hitboxes = true, targethitboxes = true }
}
local HITBOX_NAMES = { head = true, neck = true, chest = true, upperchest = true, lowerchest = true,
    stomach = true, pelvis = true, body = true, arms = true, legs = true, feet = true,
    arm = true, leg = true, foot = true, hands = true, thighs = true, calves = true }

function RB.trim(s) return (s:gsub("^%s+", ""):gsub("%s+$", "")) end
function RB.token(s) return (lower(s):gsub("[^a-z0-9]", "")) end

function RB.path_matches(kind, path)
    if not KEYS[kind] or type(path) ~= "string" or #path > 160 or path:find("[^\32-\126]") then return false end
    local name = lower(path)
    if not name:find("rage", 1, true) or name:find("override", 1, true) or name:find("keybind", 1, true) then return false end
    local tail = name:match("[^/\\.>:]+$") or name
    return KEYS[kind][RB.token(tail)] == true
end

function RB.named_boxes(value)
    if type(value) ~= "table" or #value < 1 or #value > 32 then return false end
    local count, seen = 0, {}
    for i, v in pairs(value) do
        if not U.int(i) or i < 1 or i > #value or type(v) ~= "string" then return false end
        local name = RB.token(v)
        if not HITBOX_NAMES[name] or seen[name] then return false end
        seen[name], count = true, count + 1
    end
    return count == #value
end

function Journal.valid(kind, value)
    if kind == "hc" or kind == "dmg" then
        return U.finite(value) and value >= 0 and value <= (kind == "hc" and 100 or 130)
    elseif kind == "safe" or kind == "baim" then return type(value) == "boolean"
    elseif kind == "hitbox" then return RB.named_boxes(value) end
    return false
end

function Journal.read(path, kind)
    if not path or not config then return nil end
    local value = U.safe(config.get, path)
    if Journal.valid(kind, value) then return value end
end

function Journal.save(entries)
    local data = {}
    for path, entry in pairs(entries) do
        data[path] = { kind = entry.kind, base = entry.base, previous = entry.previous, wanted = entry.wanted }
    end
    if db and U.safe(db.save, META.journal, { v = 1, paths = data }) == true then
        Journal.dirty, Journal.failed_at = false, nil
        return true
    end
    Journal.failed_at = S.rt
    U.report("config journal", "write failed; new overrides were not applied")
    return false
end

function Journal.checkpoint(force)
    if not Journal.dirty then return true end
    if not force and U.age(Journal.failed_at, S.rt) < K.RETRY then return false end
    return Journal.save(Journal.entries)
end

function Journal.forget(path)
    Journal.entries[path], Journal.dirty = nil, true
end

function Journal.restore_one(path, e, force)
    if not force and U.age(e.retry_at, S.rt) < 0.35 then return end
    e.retry_at = S.rt
    local current = Journal.read(path, e.kind)
    if current == nil then
        U.report("config restore", "cannot read " .. path .. "; saved recovery intent retained")
        return
    end
    if U.same(current, e.base) then Journal.forget(path) return end
    local ours
    if e.last ~= nil then ours = U.same(current, e.last)
    else ours = U.same(current, e.previous) or U.same(current, e.wanted) end
    if not ours then
        Journal.forget(path)
        U.report("config restore", "external edit preserved: " .. path)
        return
    end
    if U.safe(config.set, path, U.copy(e.base)) == true and U.same(Journal.read(path, e.kind), e.base) then
        Journal.forget(path)
    else
        U.report("config restore", "could not verify " .. path .. "; saved recovery intent retained")
    end
end

function Journal.release(wanted, force)
    for path, entry in pairs(Journal.entries) do
        if not wanted or not wanted[path] or entry.recovery then Journal.restore_one(path, entry, force) end
    end
    Journal.checkpoint(force)
end

function Journal.upkeep()
    for path, entry in pairs(Journal.entries) do
        if entry.recovery then Journal.restore_one(path, entry, false) end
    end
    Journal.checkpoint(false)
end

function Journal.init()
    Journal.entries, Journal.blocked, Journal.dirty = {}, {}, false
    local data = db and U.safe(db.load, META.journal, nil)
    if type(data) ~= "table" or data.v ~= 1 or type(data.paths) ~= "table" then return end
    local n = 0
    for path, entry in pairs(data.paths) do
        if type(entry) == "table" and RB.path_matches(entry.kind, path) and Journal.valid(entry.kind, entry.base)
            and Journal.valid(entry.kind, entry.previous) and Journal.valid(entry.kind, entry.wanted) then
            Journal.entries[path] = { kind = entry.kind, base = entry.base, previous = entry.previous,
                wanted = entry.wanted, recovery = true }
            n = n + 1
            if n >= 20 then break end
        end
    end
    Journal.release(nil, true)
end

function Journal.original(path, kind)
    if not path then return nil end
    local entry = Journal.entries[path]
    if entry then return U.copy(entry.base) end
    return Journal.read(path, kind)
end

function Journal.set(path, kind, wanted)
    if not path or Journal.blocked[path] or not Journal.valid(kind, wanted) then return false end
    local entry, current = Journal.entries[path], Journal.read(path, kind)
    if current == nil or (entry and (entry.kind ~= kind or entry.recovery)) then return false end
    if entry and entry.last ~= nil and not U.same(current, entry.last) then
        Journal.forget(path)
        Journal.blocked[path] = true
        U.report("config verify", "path yielded to an external edit: " .. path)
        return false
    end
    if U.same(current, wanted) then return true end
    if U.age(Journal.failed_at, S.rt) < K.RETRY then return false end

    -- Save the before/after intent first so either value can be recovered after an interruption.
    local base = current
    if entry then base = entry.base end
    local proposal = { kind = kind, base = U.copy(base), previous = U.copy(current), wanted = U.copy(wanted) }
    local staged = U.copy(Journal.entries)
    staged[path] = proposal
    if not Journal.save(staged) then return false end
    Journal.entries = staged
    local accepted = U.safe(config.set, path, U.copy(wanted)) == true
    local observed = Journal.read(path, kind)
    if U.same(observed, wanted) then
        proposal.last = U.copy(observed)
        if accepted then
            if CFG.log_cfg then U.say("set " .. path .. " (" .. tostring(kind) .. ")") end
            return true
        end
        Journal.blocked[path], proposal.recovery = true, true
    elseif U.same(observed, current) then
        Journal.entries[path], Journal.dirty = entry, true
        Journal.blocked[path] = true
    else
        proposal.recovery, Journal.blocked[path] = true, true
    end
    U.report("config set", "could not verify " .. path)
    return false
end

function RB.discover()
    Journal.release(nil, true)
    Journal.blocked = {}
    RB.paths, RB.path_count = {}, 0
    RB.evaluated = nil
    local keys = config and U.safe(config.keys)
    if type(keys) ~= "table" then RB.status = "Config keys unavailable" return end
    for _, kind in ipairs(SLOTS) do
        local explicit = RB.trim(CFG["path_" .. kind] or "")
        local one, count = nil, 0
        local seen = {}
        for _, path in ipairs(keys) do
            if (explicit == "" or path == explicit) and RB.path_matches(kind, path) and not seen[path]
                and Journal.read(path, kind) ~= nil then
                seen[path], one, count = true, path, count + 1
                if count > 1 then break end
            end
        end
        if count == 1 then RB.paths[kind], RB.path_count = one, RB.path_count + 1
        elseif explicit ~= "" then U.say("unavailable " .. kind .. " path: " .. explicit) end
    end
    RB.status = RB.path_count == 0 and "No compatible paths" or (RB.path_count .. "/5 config paths linked")
    U.say(RB.status)
end

function RB.damage(from, to, pawn, group)
    if not to then return 0, false end
    local result = U.safe(trace.bullet, from, to, pawn, group)
    if type(result) == "table" then
        local p = result.penetrated
        local direct = p == false or p == 0
        if result.target_hit == true and U.finite(result.target_damage) then
            return max(0, result.target_damage), direct
        end
        if result.hit == true and U.addr(result.entity) == U.addr(pawn) and U.finite(result.damage) then
            return max(0, result.damage), direct
        end
        if result.target_hit == false or result.hit == false then return 0, false end
    end
    local damage = U.safe(trace.damage, pawn, to)
    return U.finite(damage) and max(0, damage) or 0, false
end

function RB.evaluate(from, view)
    local candidates, players = {}, U.safe(entity.players)
    if type(players) ~= "table" then return nil end
    for _, row in ipairs(players) do
        local p = type(row) == "table" and row.pawn or nil
        if U.call(p, "alive") == true and U.call(p, "is_enemy") == true then
            local addr = U.addr(p)
            local rec = addr and RES.by_addr[addr]
            local eye = RES.present(rec) and U.call(p, "eye_position")
            if U.vec(eye) and rec.key == RES.identity(row.controller, p) then
                local fov = U.fov(from, eye, view)
                if fov <= CFG.baim_fov then
                    local at = #candidates + 1
                    while at > 1 do
                        local previous = candidates[at - 1]
                        if fov > previous.fov or (fov == previous.fov and addr > previous.rec.addr) then break end
                        candidates[at] = previous
                        at = at - 1
                    end
                    candidates[at] = { rec = rec, p = p, fov = fov }
                    candidates[K.MAX_TARGETS + 1] = nil
                end
            end
        end
    end
    local best, best_score
    for i = 1, #candidates do
        local c = candidates[i]
        local hp = U.call(c.p, "health")
        if U.finite(hp) and hp > 0 then
            local h = HB.indices(c.p, c.rec)
            local head, direct_h = RB.damage(from, HB.point(c.p, h.head, true), c.p, K.HEAD)
            local chest, direct_c = RB.damage(from, HB.point(c.p, h.chest), c.p, K.CHEST)
            local stomach, direct_s = RB.damage(from, HB.point(c.p, h.stomach), c.p, K.STOMACH)
            local body = max(chest, stomach)
            local dmg = max(body, head)
            local direct = (direct_h and head >= 3) or (direct_c and chest >= 3) or (direct_s and stomach >= 3)
            if dmg > 0 then
                local score = min(1.5, dmg / hp) + (direct and 1 or 0) + (dmg >= hp and 0.75 or 0)
                    - c.fov / max(1, CFG.baim_fov) * 0.20
                if not best_score or score > best_score then
                    best_score = score
                    local flags = U.call(c.p, "flags")
                    local vel = U.call(c.p, "velocity")
                    best = { rec = c.rec, hp = hp, hd = head, bd = body, air = U.call(c.p, "on_ground") == false,
                        duck = U.int(flags) and bit.band(flags, 2) ~= 0,
                        speed = U.vec(vel) and sqrt(vel.x * vel.x + vel.y * vel.y) or 0 }
                end
            end
        end
    end
    return best
end

function RB.near(from, view)
    local best, value = nil, 15
    for _, rec in pairs(RES.by_addr) do
        if RES.present(rec) then
            local f = U.fov(from, rec.eye, view)
            if f < value or (best and f == value and rec.addr < best.addr) then best, value = rec, f end
        end
    end
    return best
end

function RB.move_state(pawn)
    local ground, vel = U.call(pawn, "on_ground"), U.call(pawn, "velocity")
    if type(ground) ~= "boolean" or not U.vec(vel) then return nil end
    local air = not ground
    if air and CFG.air_mode == 1 and not RB.was_air and abs(vel.z) < CFG.air_thr then air = false end
    RB.was_air = air
    if air and CFG.air_mode == 3 then
        local result = U.safe(engine.simulate, CFG.land_ticks)
        if type(result) == "table" then
            for i = 1, #result do
                local step = result[i]
                if type(step) == "table" and step.valid == true and step.on_ground == true then
                    air = false
                    break
                end
            end
        end
    end
    if air then return CFG.apex_on and abs(vel.z) <= CFG.apex_win and "APEX" or "AIR" end
    local flags = U.call(pawn, "flags")
    if U.int(flags) and bit.band(flags, 2) ~= 0 then return "DUCK" end
    local speed = vel.x * vel.x + vel.y * vel.y
    if speed < 25 then return "STAND" end
    return speed <= 19600 and "WALK" or "RUN"
end

function RB.bind(key)
    return UI[key] and U.call(UI[key].el, "active") == true
end

function RB.head_boxes(original, head_only)
    if not RB.named_boxes(original) then return nil, false end
    local out, head = {}, false
    for i = 1, #original do
        local name = RB.token(original[i])
        if name == "head" then head = true end
        if (head_only and name == "head") or (not head_only and name ~= "head" and name ~= "neck") then
            out[#out + 1] = original[i]
        end
    end
    if #out > 0 then return out, head end
    return nil, head
end

function RB.trust(rec)
    if not RES.ready(rec) then return 0 end
    local m = rec.class
    return U.bound(rec.conf * 0.72 + m.confidence * 0.21 + min(3, rec.hit_streak) * 0.04
        - rec.miss_streak * 0.1 - (rec.index - 1) * 0.025, 0, 1)
end

function RB.decide(ctx, movement)
    local p = RB.paths
    local wanted = {}
    local function put(kind, val)
        local path = p[kind]
        if not path or val == nil then return false end
        wanted[path] = true
        return Journal.set(path, kind, val)
    end

    local head, body, hs_effective, body_effective = false, false, false, false
    local dmg_original = Journal.original(p.dmg, "dmg")
    local boxes = Journal.original(p.hitbox, "hitbox")
    local dmg, gate
    local strict, force_dmg, force_body, force_head = RB.bind("k_strict"), RB.bind("k_dmg"), RB.bind("k_baim"), RB.bind("k_head")
    local in_air = movement == "AIR" or movement == "APEX"

    if force_dmg then dmg = CFG.dmg_bind_val
    elseif in_air and CFG.air_on then dmg = CFG.air_dmg end
    if ctx then
        local rec, bd, hd, hp = ctx.rec, ctx.bd, ctx.hd, ctx.hp
        local lc = U.age(rec.lc, S.rt) < K.LC_HOLD
        local suspect = rec.miss_streak >= 2 or rec.index >= 3 or rec.class.name == "random"
            or (rec.class.name == "jitter" and (rec.class.amp or 0) > 35)
        body = bd > 0 and (force_body or (CFG.baim_on and (
            (CFG.baim_lethal and bd >= hp + CFG.baim_margin) or (CFG.baim_2x and 2 * bd >= hp and hd < hp)
            or (CFG.baim_hp_on and hp <= CFG.baim_hp) or (CFG.baim_unres and (lc or (suspect and RB.trust(rec) < 0.52)))
        )))
        local state = ctx.speed < 4 and "Standing" or (ctx.speed <= 140 and "Walking" or "Running")
        if ctx.duck then state = "Ducking" end
        if hd > 0 and not force_body then
            if force_head then head, body = true, false
            elseif not body and CFG.hs_on and not ctx.air and not lc and CFG.hs_states[state]
                and not (CFG.hs_body_first and bd >= hp) and RB.trust(rec) >= CFG.hs_trust / 100 then
                head = CFG.hs_need == 3 or hd >= hp or (CFG.hs_need == 2 and hd >= bd * 1.25)
            end
        end
        if body then
            local body_boxes = RB.head_boxes(boxes, false)
            local by_boxes = body_boxes and put("hitbox", body_boxes)
            local by_config = put("baim", true)
            body_effective = by_boxes or by_config == true
        elseif head then
            local head_boxes, enabled = RB.head_boxes(boxes, true)
            local body_override = p.baim and Journal.entries[p.baim]
            if body_override then Journal.restore_one(p.baim, body_override, true) end
            local body_on = Journal.read(p.baim, "baim") == true or (p.baim and Journal.entries[p.baim] ~= nil)
            if not body_on and head_boxes and enabled then hs_effective = put("hitbox", head_boxes) end
            if not body_on and not hs_effective and not force_dmg and CFG.hs_gate and p.dmg and bd > 0
                and (not boxes or enabled) then
                local target = max(floor(bd) + 1, dmg or dmg_original or 0)
                if target <= hp and target <= hd and target <= 130 then gate, dmg = target, target end
            end
        end
        if CFG.dmg_cap and not force_dmg and (dmg or dmg_original or 0) > hp then dmg = hp end
    end
    if dmg then
        local damage_set = put("dmg", dmg)
        if gate and damage_set and dmg >= gate then hs_effective = true end
    end
    if strict or (CFG.air_on and in_air and CFG.air_safe) then put("safe", true) end

    local original_hc = Journal.original(p.hc, "hc")
    if U.finite(original_hc) then
        local states = { STAND = CFG.hc_stand, WALK = CFG.hc_slow, RUN = CFG.hc_move, DUCK = CFG.hc_duck }
        local base = original_hc
        if CFG.air_on and in_air then base = movement == "APEX" and CFG.apex_hc or CFG.air_hc
        elseif CFG.hc_on and (states[movement] or 0) > 0 then base = states[movement] end
        local add = (hs_effective and CFG.hs_hc or 0) + (strict and CFG.strict_bonus or 0)
        if ctx then
            if ctx.air then add = add + CFG.hc_tgt_air
            elseif ctx.speed > 140 then add = add + CFG.hc_tgt_move end
            if CFG.enable and RES.ready(ctx.rec) and RB.trust(ctx.rec) < 0.45 then add = add + CFG.unres_hc end
        end
        local value = U.round(U.bound(base + add, 0, add > 0 and max(base, CFG.hc_cap) or 100))
        if value ~= original_hc then put("hc", value) end
    end
    Journal.release(wanted, false)
    RB.head, RB.body = hs_effective == true, body_effective == true
end

function RB.stand_down(reason, force)
    RB.target, RB.focus, RB.focus_at, RB.evaluated = nil, nil, nil, nil
    RB.head, RB.body, RB.was_air = false, false, false
    RB.status = reason
    Journal.release(nil, force == true)
end

function RB.update(me, from, view, info)
    local group = info and (WEAPON_GROUP[info.def] or 6)
    local enabled = CFG.rb_enable and (not CFG.pause_menu or not S.menu) and group and CFG.weapons[group] == true
    if not enabled then
        local reason = CFG.rb_enable and (S.menu and CFG.pause_menu and "Menu paused" or "Weapon not selected") or "Assist off"
        if RB.status ~= reason then
            Journal.blocked = {}
            RB.stand_down(reason)
        elseif next(Journal.entries) then Journal.release(nil, false) end
        if U.age(RB.focus_at, S.rt) >= K.EVAL_EVERY then
            RB.focus_at = S.rt
            RB.focus = CFG.enable and RB.near(from, view) or nil
        end
        return
    end
    if RB.weapon ~= info.def then
        RB.stand_down("Weapon changed", true)
        Journal.blocked, RB.weapon = {}, info.def
    end
    if U.age(RB.evaluated, S.rt) < K.EVAL_EVERY then return end
    RB.evaluated = S.rt
    local movement = RB.move_state(me)
    if not movement then RB.stand_down("Movement unavailable") return end
    local ctx = RB.evaluate(from, view)
    RB.target, RB.move = ctx and ctx.rec, movement
    RB.focus = RB.target or (CFG.enable and RB.near(from, view))
    RB.decide(ctx, movement)
    RB.status = RB.path_count == 0 and "No compatible paths" or (RB.path_count .. "/5 config paths linked")
end

-- Menu descriptors use one-based values internally. Runtime widgets are calibrated once.
local WEAPON_ITEMS = { "SSG 08", "AWP", "Auto snipers", "Deagle / R8", "Pistols", "Other" }
local STANCE_ITEMS = { "Standing", "Ducking", "Walking", "Running" }
local PRESETS = {
    { },
    { air_hc = 70, apex_hc = 58, air_dmg = 50, hc_stand = 70, hc_slow = 65, hc_move = 55,
        hc_duck = 72, hc_tgt_air = -8, hc_tgt_move = 0, strict_bonus = 12, baim_margin = 2, baim_2x = false },
    { air_hc = 58, apex_hc = 48, air_dmg = 38, hc_stand = 60, hc_slow = 55, hc_move = 45,
        hc_duck = 62, hc_tgt_air = -12, hc_tgt_move = -4, strict_bonus = 8, baim_margin = 0, baim_2x = true },
    { air_hc = 78, apex_hc = 68, air_dmg = 62, hc_stand = 80, hc_slow = 75, hc_move = 66,
        hc_duck = 82, hc_tgt_air = -4, hc_tgt_move = 0, strict_bonus = 16, baim_margin = 5, baim_2x = false }
}

local MENU = {
    { "0x Resolver", {
        { "Delivery", {
            { "enable", "Enable resolver", false }, { "cmd_fix", "Correct firing commands", true },
            { "rotate_move", "Preserve movement when rotating view", true },
            { "mem_write", "Experimental eye-angle write (insecure)", false },
            { "k_flip", "Flip focus side", "keybind" }
        } },
        { "Model", {
            { "mode", "Resolver mode", 1, { "Adaptive", "Static side", "Bruteforce", "Jitter / Spin", "Static offset" } },
            { "base", "Yaw base", 1, { "Auto", "Eye yaw", "At target" } },
            { "pitch", "Memory-channel pitch", 3, { "Off", "Clamp", "Auto", "Force down", "Force zero", "Force up" } },
            { "desync", "Maximum desync", 58, 0, 90 }, { "yaw_off", "Static yaw offset", 0, -180, 180 },
            { "move_sc", "Moving correction %", 35, 0, 100 }, { "face_damp", "Dampen while facing target", true },
            { "jit_mode", "Jitter handling", 1, { "Center", "Predict next", "Follow last" } },
            { "jit_sc", "Jitter correction %", 50, 0, 100 },
            { "brute_pat", "Brute pattern", 1, { "Multipliers", "Stepped" } },
            { "brute_step", "Brute step", 30, 5, 90 }, { "brute_skip", "Skip recent failed offsets", true }
        } },
        { "Hints", {
            { "body", "Body yaw hint", true }, { "scene_hint", "Prefer scene-node hint (insecure)", false },
            { "freestand", "Freestanding hint", true }, { "move_mem", "Movement memory", true },
            { "move_dir", "Movement direction", true }, { "lc_detect", "Watch simulation discontinuities", true },
            { "lc_hold", "Hold history on discontinuity", true }
        } },
        { "Learning", {
            { "feedback", "Learn from game events", true }, { "miss_win", "Miss window (ms)", 350, 150, 1000 },
            { "miss_tol", "Weighted misses before stepping", 1, 1, 3 }, { "spread_blame", "Reduce credit for wide spread", true },
            { "body_partial", "Body hit while aiming head is partial", true },
            { "anti_ab", "Anticipate repeated side flips", true }, { "cls_mem", "Side memory by yaw class", true },
            { "hint_learn", "Learn hint reliability", true }, { "flip_on_hurt", "Flip when opponent hits you", false },
            { "persist", "Store human learning locally", true }
        } }
    } },
    { "0x Rage", {
        { "Assist", {
            { "rb_enable", "Enable config assist", false }, { "pause_menu", "Pause in menu", true },
            { "preset", "Preset", 2, { "Custom", "Balanced", "Aggressive", "Conservative" } },
            { "weapons", "Weapon groups", { true, true, true, true, true, false }, WEAPON_ITEMS },
            { "baim_fov", "Target search FOV", 60, 5, 180 }, { "dmg_cap", "Cap damage threshold at target HP", true },
            { "log_cfg", "Log verified config writes", false }
        } },
        { "Accuracy", {
            { "hc_on", "Hitchance by movement", true }, { "hc_stand", "Standing hitchance", 70, 0, 100 },
            { "hc_slow", "Walking hitchance", 65, 0, 100 }, { "hc_move", "Running hitchance", 55, 0, 100 },
            { "hc_duck", "Ducking hitchance", 72, 0, 100 }, { "hc_cap", "Stacked hitchance cap", 95, 50, 100 },
            { "hc_tgt_air", "Airborne target adjustment", -8, -30, 30 },
            { "hc_tgt_move", "Running target adjustment", 0, -30, 30 },
            { "unres_hc", "Low-trust target adjustment", 8, -30, 30 },
            { "k_strict", "Strict accuracy bind", "keybind" }, { "strict_bonus", "Strict hitchance bonus", 12, 0, 40 },
            { "k_dmg", "Damage override bind", "keybind" }, { "dmg_bind_val", "Bound damage override", 30, 1, 130 }
        } },
        { "Jump", {
            { "air_on", "Jump optimizer", true }, { "air_hc", "Air hitchance", 70, 1, 100 },
            { "air_dmg", "Air damage", 50, 1, 130 }, { "air_safe", "Air safepoint", true },
            { "apex_on", "Use apex hitchance", true }, { "apex_hc", "Apex hitchance", 58, 1, 100 },
            { "apex_win", "Apex vertical speed window", 42, 10, 110 },
            { "air_mode", "Air detection", 1, { "Ground + vertical speed", "Ground flag only", "Landing prediction" } },
            { "air_thr", "Air vertical speed threshold", 22, 5, 220 }, { "land_ticks", "Landing lead ticks", 3, 1, 8 }
        } },
        { "Hitboxes", {
            { "hs_on", "Headshot assist", false }, { "hs_trust", "Minimum resolver trust %", 62, 30, 95 },
            { "hs_need", "Prefer head when", 2, { "Head shot is lethal", "Head beats body", "Whenever trusted" } },
            { "hs_states", "Headshot target states", { true, true, true, false }, STANCE_ITEMS },
            { "hs_body_first", "Prefer lethal body shot", true }, { "hs_hc", "Head hitchance bonus", 6, 0, 25 },
            { "hs_gate", "Allow measured damage gate", true }, { "k_head", "Force head bind", "keybind" },
            { "baim_on", "Smart body aim", true }, { "baim_lethal", "Body kills in one shot", true },
            { "baim_2x", "Body kills in two shots", false }, { "baim_margin", "Body damage margin", 2, 0, 30 },
            { "baim_hp_on", "Prefer body at low HP", false }, { "baim_hp", "Low HP cutoff", 40, 1, 100 },
            { "baim_unres", "Prefer body against low trust", true }, { "k_baim", "Force body bind", "keybind" }
        } },
        { "Config link", {
            { "path_hc", "Exact hitchance path", "" }, { "path_dmg", "Exact damage path", "" },
            { "path_safe", "Exact safepoint path", "" }, { "path_baim", "Exact body-aim path", "" },
            { "path_hitbox", "Exact hitboxes path", "" },
            { "rescan", "Rescan config paths", "button" }, { "dump", "Print compatible config paths", "button" }
        } }
    } },
    { "0x Visuals", {
        { "Display", {
            { "panel", "Status panel", true }, { "overlay", "Yaw class over players", true },
            { "ov_style", "Overlay style", 1, { "Compact", "Detailed" } }, { "yaw_lines", "Yaw direction lines", false },
            { "feed", "Recent shot outcomes", true }, { "log_hits", "Log shots to console", false },
            { "panel_x", "Panel X %", 1, 0, 100 }, { "panel_y", "Panel Y %", 40, 0, 100 },
            { "panel_scale", "Panel scale %", 100, 80, 150 }
        } }
    } },
    { "0x Config", {
        { "Persistence", {
            { "persist_ui", "Remember settings", true }, { "notif", "Notifications", true },
            { "export", "Export settings to 0x_export.json", "button" },
            { "import_db", "Import 0x_import.json", "button" }, { "import_text", "Paste settings JSON", "" },
            { "import_paste", "Import pasted JSON", "button" }, { "reset_ui", "Reset settings to defaults", "button" },
            { "reset_learn", "Clear learning and shot totals", "button" }
        } }
    } }
}

function Menu.multi(value, items)
    if type(value) ~= "table" then return nil end
    local out = {}
    for k, v in pairs(value) do
        if type(v) ~= "boolean" then return nil end
        if U.int(k) then
            if k < 1 or k > #items then return nil end
        else
            local found = false
            for i = 1, #items do if k == items[i] then found = true break end end
            if not found then return nil end
        end
    end
    for i = 1, #items do
        local v = value[items[i]]
        if type(v) ~= "boolean" then v = value[i] end
        out[i], out[items[i]] = v == true, v == true
    end
    return out
end

function Menu.config_value(row, value)
    if row.kind == "checkbox" then
        if type(value) == "boolean" then return value end
    elseif row.kind == "slider_int" then
        if U.finite(value) then return U.bound(U.round(value), row.lo, row.hi) end
    elseif row.kind == "combo" then
        if U.int(value) and value >= 1 and value <= #row.items then return value end
        for i = 1, #row.items do if value == row.items[i] then return i end end
    elseif row.kind == "multi_combo" then
        return Menu.multi(value, row.items)
    elseif row.kind == "text" and type(value) == "string" and #value <= row.max then
        return value
    end
end

function Menu.calibrate(row)
    local el, size = row.el, #row.items
    local before = U.call(el, "get")
    U.call(el, "set", 1)
    local one = U.call(el, "get")
    if type(one) == "string" then
        if one == row.items[1] then row.base = 1
        elseif one == row.items[2] then row.base = 0 end
    elseif U.int(one) then
        U.call(el, "set", 0)
        local zero = U.call(el, "get")
        U.call(el, "set", size)
        local last = U.call(el, "get")
        if zero == 0 and last ~= size then row.base = 0
        elseif zero ~= 0 and last == size then row.base = 1 end
    end
    if row.base ~= nil then U.call(el, "set", row.def + row.base - 1)
    else
        if before ~= nil then U.call(el, "set", before) end
        row.inert = true
        U.call(el, "inactive", true, "Combo index base could not be verified")
        U.report("menu " .. row.id, "ambiguous combo index base")
    end
end

function Menu.read(row)
    if not row.el or row.inert then return nil end
    local ok, v = pcall(invoke, row.el, "get")
    if not ok then U.report("menu " .. row.id, v) return nil end
    if row.kind == "combo" and U.int(v) then v = v - row.base + 1 end
    return Menu.config_value(row, v)
end

function Menu.set(row, requested)
    local v = Menu.config_value(row, requested)
    if v == nil or not row.el or row.inert then return false end
    local native = v
    if row.kind == "combo" then native = v + row.base - 1
    elseif row.kind == "multi_combo" then
        native = {}
        for i = 1, #row.items do native[i] = v[i] end
    end
    local ok, result = pcall(invoke, row.el, "set", native)
    local got = Menu.read(row)
    if not ok or result == false or (got == nil or not U.same(got, v)) then
        U.report("menu " .. row.id, "value change could not be verified")
        if got ~= nil then CFG[row.id] = got end
        return false
    end
    CFG[row.id] = got
    return true
end

function Menu.changed(row)
    if Menu.syncing or not S.booted then return end
    local v = Menu.read(row)
    if v == nil or U.same(CFG[row.id], v) then return end
    CFG[row.id] = v
    Menu.syncing = true
    if row.id == "preset" then
        for key, val in pairs(PRESETS[v]) do Menu.set(UI[key], val) end
    elseif (CFG.preset or 1) > 1 and PRESETS[2][row.id] ~= nil then
        Menu.set(UI.preset, 1)
    end
    Menu.syncing = false
    LIFE.settings_changed(row.id)
end

function Menu.register(group, descriptor)
    local id, label, def, lo, hi = descriptor[1], descriptor[2], descriptor[3], descriptor[4], descriptor[5]
    local t, ctor, widget = type(def), nil, nil
    local row = { id = id, def = def }
    if t == "boolean" then ctor, widget = "checkbox", U.call(group, "checkbox", label, def)
    elseif t == "number" and type(lo) == "table" then
        ctor, widget, row.items = "combo", U.call(group, "combo", label, lo, def), lo
    elseif t == "number" then
        ctor, widget, row.lo, row.hi = "slider_int", U.call(group, "slider_int", label, lo, hi, def, "%d"), lo, hi
    elseif t == "table" then
        ctor, widget, row.items = "multi_combo", U.call(group, "multi_combo", label, lo, def), lo
    elseif def == "keybind" then ctor, widget = "keybind", U.call(group, "keybind", label, 0)
    elseif def == "button" then
        ctor, widget = "button", U.call(group, "button", label, function()
            if not S.booted then return end
            LIFE.clock()
            U.guard("action " .. id, IO.actions[id])
        end)
    else
        ctor, widget, row.max = "text", U.call(group, "text", label, def), id == "import_text" and 65536 or 160
    end
    row.kind, row.el = ctor, widget
    UI[id] = row
    if not widget then U.report("menu " .. id, "control unavailable") end
    if ctor == "button" or ctor == "keybind" or id == "import_text" then return end
    Menu.order[#Menu.order + 1] = row
    if widget and ctor == "combo" then Menu.calibrate(row) end
    CFG[id] = Menu.config_value(row, def)
    if widget and not row.inert then
        if id == "mem_write" or id == "scene_hint" then Menu.set(row, false) end
        local current = Menu.read(row)
        if current ~= nil then CFG[id] = current end
        local ok, result = pcall(invoke, widget, "callback", function()
            LIFE.clock()
            U.guard("menu callback " .. id, Menu.changed, row)
        end)
        if not ok or result == false then
            Menu.poll_rows[#Menu.poll_rows + 1] = row
            U.report("menu callback " .. id, "using periodic reads")
        end
    end
end

function Menu.build()
    Menu.order, Menu.poll_rows = {}, {}
    for i = 1, #MENU do
        local spec = MENU[i]
        local tab = U.safe(ui.tab, spec[1])
        for _, group in ipairs(spec[2]) do
            local controls = U.call(tab, "group", group[1])
            for _, item in ipairs(group[2]) do Menu.register(controls, item) end
        end
    end
    U.call(U.call(U.safe(ui.tab, "0x About"), "group", "Runtime"), "label",
        "0x " .. META.version .. " / Live status in the paint panel")
end

function Menu.poll()
    if U.age(Menu.poll_at, S.rt) < 0.75 then return end
    Menu.poll_at = S.rt
    for i = 1, #Menu.poll_rows do U.guard("menu poll", Menu.changed, Menu.poll_rows[i]) end
end

function Menu.memory_controls()
    local insecure = Schema.insecure()
    S.insecure = insecure
    if Menu.insecure == insecure then return end
    Menu.insecure = insecure
    for _, id in ipairs({ "mem_write", "scene_hint" }) do
        U.call(UI[id].el, "inactive", not insecure, "Requires Allow Insecure")
    end
end

function IO.notice(message)
    U.say(message)
    if CFG.notif and client then U.safe(client.notify, message, "0x") end
end

function IO.snapshot(export)
    local bag = { persist_ui = CFG.persist_ui == true }
    if export or CFG.persist_ui then
        for _, row in ipairs(Menu.order) do
            local id, value = row.id, CFG[row.id]
            if id ~= "mem_write" and id ~= "scene_hint" then
                if row.kind == "multi_combo" then
                    local map = {}
                    for _, item in ipairs(row.items) do map[item] = value[item] == true end
                    bag[id] = map
                else bag[id] = value end
            end
        end
    end
    return { v = META.schema, ver = META.version, persist = CFG.persist_ui == true, s = bag }
end

function IO.apply(data, startup)
    if type(data) ~= "table" or type(data.s) ~= "table" or not U.int(data.v) or data.v < 1 or data.v > META.schema then
        return nil
    end
    local count = 0
    Menu.syncing = true
    if startup and data.persist == false then
        Menu.set(UI.persist_ui, false)
    else
        for _, row in ipairs(Menu.order) do
            if row.id ~= "mem_write" and row.id ~= "scene_hint" and data.s[row.id] ~= nil then
                if Menu.set(row, data.s[row.id]) then count = count + 1 end
            end
        end
        if type(data.paths) == "table" then
            for _, kind in ipairs(SLOTS) do
                local path = data.paths[kind]
                if type(path) == "table" and #path == 1 then path = path[1] end
                local id = "path_" .. kind
                if data.s[id] == nil and RB.path_matches(kind, path) and Menu.set(UI[id], path) then count = count + 1 end
            end
        end
    end
    Menu.syncing = false
    return count
end

function IO.load()
    if not db then return end
    local data = U.safe(db.load, META.settings, nil)
    if IO.apply(data, true) ~= nil then return end
    for _, old in ipairs(META.previous) do
        data = U.safe(db.load, old, nil)
        if IO.apply(data, true) ~= nil then
            U.say("migrated compatible settings from " .. old)
            IO.dirty_at = S.rt
            return
        end
    end
end

function IO.flush(force)
    if not IO.dirty_at then return true end
    if not force and (U.age(IO.dirty_at, S.rt) < 1.5 or U.age(IO.failed_at, S.rt) < K.RETRY) then return false end
    if db and U.safe(db.save, META.settings, IO.snapshot(false)) == true then
        IO.dirty_at, IO.failed_at = nil, nil
        return true
    end
    IO.failed_at = S.rt
    U.report("settings", "save failed; changes retained for retry")
    return false
end

function IO.import(data)
    local n = IO.apply(data, false)
    if n == nil then IO.notice("Invalid or unsupported settings snapshot") return end
    LIFE.settings_changed(nil)
    IO.notice(format("Imported %d compatible controls", n))
end

IO.actions = {
    rescan = function() RB.discover() end,
    dump = function()
        local keys = config and U.safe(config.keys)
        if type(keys) ~= "table" then IO.notice("Config keys unavailable") return end
        for _, kind in ipairs(SLOTS) do
            for _, name in ipairs(keys) do
                if RB.path_matches(kind, name) and Journal.read(name, kind) ~= nil then U.say(kind .. ": " .. name) end
            end
        end
    end,
    export = function()
        local data = IO.snapshot(true)
        local text = json and U.safe(json.encode, data)
        if type(text) ~= "string" then IO.notice("Could not encode settings") return end
        local saved = db and U.safe(db.save, META.export, data) == true
        U.say(text)
        IO.notice(saved and "Saved data\\db\\0x_export.json" or "Export file write failed; JSON is in the console")
    end,
    import_db = function() IO.import(db and U.safe(db.load, META.import, nil)) end,
    import_paste = function()
        local text = Menu.read(UI.import_text)
        if type(text) ~= "string" or #text == 0 then IO.notice("Paste a JSON snapshot no larger than 64 KiB") return end
        IO.import(json and U.safe(json.decode, text))
    end,
    reset_ui = function()
        Menu.syncing = true
        for _, row in ipairs(Menu.order) do Menu.set(row, row.def) end
        Menu.syncing = false
        LIFE.settings_changed(nil)
    end,
    reset_learn = function()
        Feedback.clear(true)
        RES.clear(true, false)
        RES.weights, RES.signs, RES.flipped = { 1, 1, 1, 1 }, { 1, 1, 1, 1 }, {}
        VIS.feed = {}
        Store.data, Store.dirty, Store.clearing, Store.count = {}, true, true, 0
        IO.notice(Store.flush(true) and "Learning cleared" or "Session cleared; on-disk clear will retry")
    end
}

function VIS.init()
    local font = U.safe(render.font, "segoeui.ttf", 13)
    if U.call(font, "loaded") == true then VIS.font = font end
    VIS.fg, VIS.muted, VIS.accent = color(236, 236, 232), color(170, 172, 165), color(210, 227, 171)
    VIS.bg, VIS.line, VIS.bad = color(19, 20, 18, 230), color(94, 98, 89), color(238, 157, 140)
    VIS.feed = {}
end

function VIS.push(kind, text)
    if CFG.log_hits then U.say(kind .. " / " .. text) end
    local feed = VIS.feed
    if #feed >= 4 then remove(feed, 1) end
    feed[#feed + 1] = { t = S.rt, kind = kind, text = text }
end

function VIS.is_applied(rec)
    return rec and ((CFG.cmd_fix and U.age(rec.applied_at, S.rt) < K.LINGER and rec.delivery)
        or (CFG.mem_write and S.insecure and rec.mem and rec.mem.verified and U.age(rec.mem.at, S.rt) <= K.STALE and "memory"))
end

function VIS.text(x, y, tint, value, size)
    render.text(x, y, tint, value, nil, size or 13, VIS.font)
end

function VIS.players()
    if not (CFG.enable and CFG.overlay) then return end
    for _, rec in pairs(RES.by_addr) do
        if RES.present(rec, K.LINGER) then
            local a = rec.eye
            local x, y = render.world_to_screen(vector(a.x, a.y, a.z + 9))
            local solved = rec.correction
            if U.finite(x) and U.finite(y) then
                local label = solved and string.upper(rec.class.name) or "SAMPLING"
                if solved and CFG.ov_style == 2 then
                    label = format("%s  %+.0f  %d%%", label, solved.offset, rec.conf * 100)
                end
                VIS.text(x + 5, y - 5, VIS.is_applied(rec) and VIS.accent or VIS.fg, label)
            end
            if CFG.yaw_lines and rec.raw and solved then
                local xx, yy = render.world_to_screen(a)
                if U.finite(xx) and U.finite(yy) then
                    for i = 1, 2 do
                        local angle = rad(i == 1 and rec.raw.y or solved.yaw)
                        local tx, ty = render.world_to_screen(vector(a.x + cos(angle) * 22, a.y + sin(angle) * 22, a.z))
                        if U.finite(tx) and U.finite(ty) then render.line(xx, yy, tx, ty, i == 1 and VIS.line or VIS.accent, 1) end
                    end
                end
            end
        end
    end
end

function VIS.panel_lines(x, y, step, size)
    local f = RB.focus
    local st, s = Feedback.stats, RB.status or "Assist off"
    local parts = (RB.head and " / HEAD" or "") .. (RB.body and " / BODY" or "")
    VIS.text(x, y + 9 * step, VIS.fg, "0x " .. META.version .. " / GAME EVENTS", size)
    VIS.text(x, y + 29 * step, VIS.muted, s .. parts, size)
    local focus = "No focus"
    if RES.present(f, K.LINGER) then
        local delivery = VIS.is_applied(f) or (RES.ready(f) and "not applied" or "sampling")
        focus = f.name .. " / " .. f.class.name .. " / " .. delivery
    end
    VIS.text(x, y + 49 * step, VIS.fg, focus, size)
    local pending = st.tracked - st.hit - st.miss - st.void
    VIS.text(x, y + 69 * step, VIS.muted,
        format("Tracked %d/%d  Hit %d  Miss %d", st.tracked, st.fired, st.hit, st.miss), size)
    VIS.text(x, y + 87 * step, VIS.muted,
        format("Pending %d  Discarded %d  Unpaired %d", pending, st.void, st.unpaired), size)
end

function VIS.paint()
    if S.active then VIS.players() end
    if not CFG.panel or not (S.active or S.menu) then return end
    local sw, sh = render.screen_size()
    if not U.finite(sw) or not U.finite(sh) then return end
    local scale = CFG.panel_scale / 100
    local w, h, pad = min(max(1, sw - 24), 328 * scale), 108 * scale, 11 * scale
    local x = 12 + max(0, sw - w - 24) * CFG.panel_x / 100
    local y = 12 + max(0, sh - h - 100) * CFG.panel_y / 100
    local size = 13 * scale
    render.rect_filled(x, y, w, h, VIS.bg, 3)
    render.line(x, y, x + w, y, VIS.accent, 1)
    render.clip_push(x + pad, y, max(0, w - pad * 2), h)
    U.guard("status text", VIS.panel_lines, x + pad, y, scale, size)
    render.clip_pop()
    if CFG.feed then
        local offset = 0
        for i = #VIS.feed, 1, -1 do
            local entry = VIS.feed[i]
            if U.age(entry.t, S.rt) < 5 then
                VIS.text(x + pad, y + h + 7 + offset, entry.kind == "MISS" and VIS.bad or VIS.accent,
                    entry.kind .. " / " .. entry.text, size)
                offset = offset + 17 * scale
            end
        end
    end
end

-- Lifecycle: cleanup paths are isolated from the sampling and drawing modules.
function LIFE.clock()
    local now = U.safe(globals.realtime)
    if not U.finite(now) then return end
    local old = S.rt
    S.rt = now
    if S.booted and old - now > K.CLOCK_SLOP then LIFE.reset("Clock reset", S.active, true, false) end
end

function LIFE.reset(reason, active, level, round)
    S.epoch, S.active = S.epoch + 1, active
    S.last_cmd, S.last_move, S.house_at, S.flip = -math.huge, nil, nil, false
    S.waiting, S.local_dead = false, false
    U.guard("assist cleanup", RB.stand_down, reason, true)
    U.guard("feedback cleanup", Feedback.clear, false)
    U.guard("resolver cleanup", RES.clear, level, round)
    U.guard("learning save", Store.flush, true)
    if level then
        CMD.failed, CMD.axis, CMD.last_axis, CMD.axis_count = false, nil, nil, 0
        Schema.offsets, Journal.blocked, S.reports = {}, {}, {}
        RB.weapon, VIS.feed = nil, {}
    end
end

local MODEL_SETTINGS = { enable = true, cmd_fix = true, mem_write = true, scene_hint = true,
    mode = true, pitch = true, base = true, desync = true, yaw_off = true, move_sc = true,
    jit_mode = true, jit_sc = true, brute_pat = true, brute_step = true, face_damp = true,
    body = true, freestand = true, move_mem = true, move_dir = true, lc_detect = true, lc_hold = true }

function LIFE.settings_changed(name)
    IO.dirty_at, RB.evaluated = S.rt, nil
    if not name or name == "feedback" or MODEL_SETTINGS[name] then Feedback.clear(false) end
    if not name or MODEL_SETTINGS[name] then RES.clear(false, false) end
    if not name or (name and name:match("^path_")) then RB.discover() end
    if not CFG.rb_enable then RB.stand_down("Assist off", true) end
    if S.menu and CFG.pause_menu then
        U.guard("settings menu restore", RB.stand_down, "Menu paused", true)
        U.guard("settings memory restore", RES.release_all)
    end
end

function LIFE.menu(open)
    if type(open) ~= "boolean" or open == S.menu then return end
    S.menu = open
    if open and CFG.pause_menu then
        U.guard("menu restore", RB.stand_down, "Menu paused", true)
        U.guard("menu memory restore", RES.release_all)
    elseif not open then RB.evaluated, Journal.blocked = nil, {} end
end

function LIFE.housekeeping()
    if U.age(S.house_at, S.rt) < 0.06 then return end
    S.house_at = S.rt
    local active = U.safe(engine.in_game)
    if type(active) == "boolean" and active ~= S.active then LIFE.reset(active and "Ready" or "Disconnected", active, true, false) end
    local open = input and U.safe(input.menu_open)
    if type(open) == "boolean" then LIFE.menu(open) end
    U.guard("insecure controls", Menu.memory_controls)
    U.guard("menu polling", Menu.poll)
    U.guard("shot expiry", Feedback.expire)
    U.guard("record purge", RES.purge)
    U.guard("settings save", IO.flush, false)
    U.guard("learning save", Store.flush, false)
    if S.active and U.age(S.last_move, S.rt) >= K.WATCHDOG then
        U.guard("command watchdog", RB.stand_down, "Waiting for commands")
        if not S.waiting then U.guard("memory watchdog", RES.release_all) end
        S.waiting = true
    elseif S.active then
        S.waiting = false
        U.guard("config recovery", Journal.upkeep)
    else
        U.guard("offline config recovery", Journal.release, nil, false)
    end
end

function LIFE.local_down(reason)
    if not S.local_dead then
        S.local_dead, S.last_cmd, S.flip = true, -math.huge, false
        U.guard("death feedback", Feedback.clear, false)
        U.guard("death memory restore", RES.release_all)
    end
    RB.stand_down(reason)
end

function LIFE.command(cmd)
    S.last_move = S.rt
    U.guard("housekeeping", LIFE.housekeeping)
    if not S.active then return end
    local lp = U.safe(entity.local_pawn)
    if U.call(lp, "alive") ~= true then
        LIFE.local_down("Local player unavailable")
        return
    end
    S.local_dead = false
    local num = U.call(cmd, "number")
    if not U.int(num) or num <= S.last_cmd then return end
    S.last_cmd = num
    local view, from = U.call(cmd, "view_angles"), U.call(lp, "eye_position")
    if not U.vec(view) or not U.vec(from) then RB.stand_down("View unavailable") return end
    local f, s = CMD.observe_move(cmd)
    local info = U.weapon(lp)
    if not U.guard("rage assist", RB.update, lp, from, view, info) then RB.stand_down("Assist error", true) end

    local flip = RB.bind("k_flip") == true
    if CFG.enable and flip and not S.flip and RES.ready(RB.focus) then
        local rec = RB.focus
        rec.manual = -(rec.manual or rec.pred_side or rec.side)
        Model.refresh(rec)
    end
    S.flip = flip

    if not CFG.enable or not info or info.can_shoot ~= true then return end
    if S.menu and CFG.pause_menu then return end
    local attack = CMD.read_attack(cmd, view)
    if not attack then return end
    local rec, ray = CMD.probe(attack, from)
    local mode = rec and CMD.fix(cmd, attack, from, rec, ray, f, s)
    Feedback.intent(info, rec, ray, mode, U.call(lp, "on_ground") == false, from)
end

function LIFE.on(name, callback)
    local ok, id = pcall(events.on, name, function(...)
        if not S.booted then return end
        LIFE.clock()
        U.guard(name, callback, ...)
    end)
    if not ok or not U.int(id) or id < 0 then error("could not subscribe to " .. name, 0) end
    LIFE.ids[#LIFE.ids + 1] = id
end

function LIFE.unload()
    S.booted, S.active = false, false
    U.guard("assist unload", RB.stand_down, "Unloading", true)
    U.guard("resolver unload", RES.clear, true, false)
    U.guard("learning unload", Store.flush, true)
    U.guard("settings unload", IO.flush, true)
    for i = #LIFE.ids, 1, -1 do U.safe(events.off, LIFE.ids[i]) end
    LIFE.ids = {}
end

function LIFE.boot()
    LIFE.ids = {}
    if not (events and ui and globals and entity and engine and render and trace and stage and buttons and bit) then
        error("requires the lowercase Neverwin Lua API", 0)
    end
    LIFE.clock()
    Menu.build()
    IO.load()
    Menu.memory_controls()
    S.active = U.safe(engine.in_game) == true
    S.menu = input and U.safe(input.menu_open) == true or false
    U.guard("learning load", Store.load)
    RES.init()
    Feedback.clear(true)
    VIS.init()
    Journal.init()
    RB.discover()
    CMD.axis_count = 0
    LIFE.on("unload", LIFE.unload)
    LIFE.on("level_init", function() LIFE.reset("Level initialized", true, true, false) end)
    LIFE.on("level_shutdown", function() LIFE.reset("Disconnected", false, true, false) end)
    LIFE.on("round_start", function() LIFE.reset("Round started", S.active, false, true) end)
    LIFE.on("weapon_fire", Feedback.weapon_fire)
    LIFE.on("player_hurt", Feedback.player_hurt)
    LIFE.on("player_death", Feedback.death)
    LIFE.on("menu_toggled", LIFE.menu)
    LIFE.on("frame_stage", function(phase)
        if phase == stage.net_update_end then
            U.guard("housekeeping", LIFE.housekeeping)
            U.guard("resolver sampling", RES.frame)
        end
    end)
    LIFE.on("createmove", LIFE.command)
    LIFE.on("paint", function()
        U.guard("housekeeping", LIFE.housekeeping)
        U.guard("status panel", VIS.paint)
    end)
    S.booted = true
    U.say(META.version .. " loaded; feedback source: CS2 game events")
end

local ok, err = pcall(LIFE.boot)
if not ok then
    U.say("boot failed: " .. tostring(err))
    if Journal.entries then U.guard("boot cleanup", Journal.release, nil, true) end
    if events then for i = #LIFE.ids, 1, -1 do U.safe(events.off, LIFE.ids[i]) end end
end