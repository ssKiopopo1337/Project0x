-- @author 0x
-- 0x resolver module (v4.5 Power Plus). Loaded by 0x.lua with require("0x_resolver").
-- The file returns a factory: the main script passes its shared context (config, helpers,
-- constants) and gets the RES table back. Nothing is written into the global namespace.
--
--   record per player -> yaw history -> AA class -> hints (scene node body yaw, freestanding,
--   movement) -> side decision -> resolved yaw
--   delivery  : RES.cmd_fix (createmove, default)  ·  RES.apply (m_angEyeAngles, optional)
--   feedback  : weapon_fire / player_hurt heuristics; an optional aim_ack extension can be
--               wired by the caller but is not part of doc&api.txt
--   learning  : hard misses (death / lost / lagcomp / local) teach nothing, soft misses
--               (off_target / airborne / moving / spread) teach with half weight
return function(X)

local META, K, E, CFG, UI, STATE, U, RB, WPN, ACT = X.META, X.K, X.E, X.CFG, X.UI, X.STATE, X.U, X.RB, X.WPN, X.ACT
local safe, clamp, lerp, round, sign, normalize = X.safe, X.clamp, X.lerp, X.round, X.sign, X.normalize
local say, notify, report, bind_on, get_weapon_info = X.say, X.notify, X.report, X.bind_on, X.get_weapon_info

local floor, abs, sqrt, atan2, sin, cos, rad, deg = math.floor, math.abs, math.sqrt, math.atan2, math.sin, math.cos, math.rad, math.deg
local max, min = math.max, math.min
local pcall, pairs, type, tostring, tonumber = pcall, pairs, type, tostring, tonumber
local format, s_lower, s_find = string.format, string.lower, string.find
local tremove, tsort = table.remove, table.sort

local RES = {}

local C = {
    HISTORY          = 24,     -- yaw samples kept per player (~375 ms @ 64 tick; fits delayed jitter)
    JITTER_MIN_DELTA = 12,     -- deg; a delta counts as "big" above this
    SPIN_MIN_RATE    = 20,     -- deg/update mean signed drift to classify as spin
    STATIC_MAX_DELTA = 3,      -- deg mean |delta| below this = static
    SWAY_MAX_DELTA   = 10,     -- deg mean |delta| below this (and not jitter) = sway
    RANDOM_CENTER_AT = 25,     -- deg mean |delta| above this -> circular mean as base
    MOVE_SPEED       = 4,      -- u/s 2D; above = moving
    MOVEDIR_SPEED    = 45,     -- u/s 2D; above = movement direction is a usable side hint
    MOVE_MEM_TIME    = 1.0,    -- s; movement memory validity after stopping
    BODY_MAX_DELTA   = 35,     -- deg; body hint saturates here
    BODY_MIN_DELTA   = 8,      -- deg; below = no hint
    BODY_SANE_DELTA  = 110,    -- deg; model yaw further than this from eye yaw = invalid sample
    BODY_EVERY       = 4,      -- fresh updates between hitbox reads (fallback only)
    FS_OFFSET        = 26,     -- u; lateral offset for freestanding traces
    FS_EVERY         = 4,      -- fresh updates between freestanding traces per player
    FACE_ANGLE       = 35,     -- deg; eye yaw this close to "at target" = probably aiming, not AA
    FACE_SCALE       = 0.3,    -- desync multiplier while facing us
    SPIN_LEAD        = 0.5,    -- updates of spin extrapolation (Jitter / Spin mode)
    REVEAL_TIME      = 0.04,   -- s; skip samples right after the enemy fired (yaw snaps to his aim)
    SHOT_DEDUPE      = 0.10,   -- s; min interval between pending shots on the same target
    LC_DIST_SQR      = 4096,   -- u^2; origin jump above 64 u between updates = LC break
    LC_HOLD          = 1.0,    -- s; LC flag stays this long after the last break
    SPREAD_BLAME     = 5.0,    -- u; spread cone radius at target distance above this blames spread
    PURGE_AFTER      = 90,     -- s; drop records not seen for this long
    PENDING_MAX      = 32,     -- max outstanding shots
    DB_MAX           = 64,     -- persisted players
    FOCUS_FOV        = 15,     -- deg; crosshair fallback for the panel / flip bind
    ACK_WAIT         = 0.9,    -- s; shot window while aim_ack delivers results
    SOFT_W           = 0.5,    -- learning weight of a soft miss
    CMD_FOV          = 10,     -- deg; a firing command aims at a record within this angle
    CMD_MIN          = 1.0,    -- deg; yaw corrections below this are ignored
    CMD_MAX          = 90,     -- deg; sanity bound: larger corrections are dropped, not clamped
    NODE_FAILS       = 12,     -- scene node reads failing in a row before the hitbox fallback takes over
    W_LEARNED        = 1.00,
    W_BODY           = 0.55,
    W_FREESTAND      = 0.40,
    W_MOVE           = 0.30,
    W_MOVEDIR        = 0.30,
    SIDE_DEADZONE    = 0.15,
    HIT_CONF_GAIN    = 0.30,
    PARTIAL_GAIN     = 0.40,   -- share of HIT_CONF_GAIN for a body hit while aiming the head
    MISS_CONF_LOSS   = 0.20,
    SOFT_CONF_LOSS   = 0.05,   -- conf loss for hard misses (not the resolver's fault)
    ROUND_CONF_DECAY = 0.85,
    JIT_PRED_CONF    = 0.6,    -- min share of regular runs to trust the jitter phase prediction
    JIT_MAX_PERIOD   = 8,      -- updates; longer holds are not treated as periodic jitter
    LC_FREEZE        = 0.2,    -- s; history is frozen this long after an LC break (Hold on LC break)
    MODE_CONFIRM     = 2,      -- consecutive classifications before the AA class switches
    HW_MIN = 0.4, HW_MAX = 1.6, HW_GAIN = 0.04, HW_LOSS = 0.06,   -- hint reliability bounds / steps
    TRIED_TTL        = 20,     -- s; a missed effective offset is not tried again for this long
    W_CLASS          = 0.50,   -- weight of the per-class side memory in the side score
    CLS_GAIN         = 0.34,   -- class memory gain per confirmed hit
    CLS_LOSS         = 0.25,   -- class memory loss per resolver miss
}

local BRUTE = { 1.0, -1.0, 0.5, -0.5, 0.0, 0.75, -0.75 }   -- x max desync; index 1 is the trusted guess
local STEP_SEQ = { 0, 1, -1, 2, -2 }                        -- x brute step
-- Jitter model candidates (x half range, toward the predicted side): index 1 is the trusted guess.
local JIT_SEQ = { [1] = { 0, 1, -1, 0.5, -0.5 }, [2] = { 1, -1, 0, 0.5, -0.5 } }
local EYE_CLASSES = { "C_CSPlayerPawn", "C_CSPlayerPawnBase", "CCSPlayerPawn" }
local NODE_FIELDS = { "m_angAbsRotation", "m_angRotation" }  -- CGameSceneNode

-- Miss reasons. Hard: nothing to learn from. Soft: learned from with half weight.
local HARD = { death = true, lost = true, lagcomp = true, ["local"] = true }
-- ragebot.Shot.result -> reason ("hit" is handled separately).
local ACK_REASON = {
    ["death"] = "death", ["player death"] = "lost", ["timeout"] = "lost", ["unregistered shot"] = "lost",
    ["damage rejection"] = "local", ["prediction error"] = "local", ["shootpos misprediction"] = "local",
    ["hitchance misprediction"] = "local", ["occlusion"] = "local",
    ["spread"] = "spread",
    ["lagcomp misprediction"] = "lagcomp", ["lagcomp failure"] = "lagcomp", ["extrapolation"] = "lagcomp",
    ["unknown"] = "resolver",           -- everything was correct and it still missed
}

RES.C, RES.MODE_LABEL = C, { static = "STATIC", sway = "SWAY", jitter = "JITTER", spin = "SPIN", random = "RANDOM" }
RES.records, RES.by_pawn, RES.pending, RES.store = {}, {}, {}, {}
RES.insecure, RES.simtime_ok = false, true
RES.body_ok, RES.body_good, RES.body_bad = true, 0, 0
RES.node_ok, RES.node_good, RES.node_bad, RES.node_field = true, 0, 0, nil
RES.last_purge, RES.store_dirty = 0, false
RES.stats = { shots = 0, hits = 0, heads = 0, misses = 0, hard = 0, soft = 0, resolver = 0, spread = 0, lagcomp = 0,
              moving = 0, airborne = 0, off_target = 0, death = 0, lost = 0, ["local"] = 0 }
RES.hw = { b = 1, fs = 1, mv = 1, md = 1 }                    -- hint reliability (session)
RES.hsign = { b = 1, fs = 1, mv = 1, md = 1 }                 -- hint sign (flipped once when the weight bottoms out)
RES.flipped = { b = false, fs = false, mv = false, md = false }
RES.ack = { n = 0, t = -1e9 }                                 -- optional aim_ack extension deliveries
RES.ack_mode = "n/a"
RES.runs = {}                                                 -- scratch: jitter run lengths
RES.write_cls, RES.write_ok, RES.write_fails = nil, nil, 0    -- write_ok: nil unknown, true working, false disabled
RES.focus = nil                                               -- the ragebot target (RB.t_addr) or the crosshair record
RES.fs_skip = {}
RES.fs_opts = { skip = RES.fs_skip, mask = E.MASK_VISIBLE }

-- ---------------------------------------------------------------- records
-- SteamID for humans; controller address for bots (stable across respawns, unlike the pawn).
function RES.player_key(ctrl, pawn)
    if ctrl then
        local sid = safe(ctrl.steam_id, ctrl)
        if type(sid) == "string" and sid ~= "" and sid ~= "0" then return sid, true end
        local ca = safe(ctrl.address, ctrl)
        if ca then return "c" .. tostring(ca), false end
    end
    if pawn then
        local pa = safe(pawn.address, pawn)
        if pa then return "p" .. tostring(pa), false end
    end
    return nil, false
end

function RES.new_record(key, is_sid)
    local rec = {
        key = key, is_sid = is_sid, name = "?",
        -- history ring buffers
        yaws = {}, pitches = {}, deltas = {}, head = 0, n = 0, dhead = 0, dn = 0,
        pitch_jit = 0, p_avg = 0, pitch_kind = "",
        -- classification
        mode = "static", mode_conf = 0, center = 0, amp = 0, spin_rate = 0, mean_abs = 0, jit_alt = 0,
        mode_cand = nil, mode_cnt = 0,
        -- jitter model: cluster half range, switch period (updates), newest side and its run length
        jit_half = 0, jit_period = 1, jit_pconf = 0, jit_side = 1, jit_run = 0, jit_k = nil,
        -- hints
        body_delta = 0, body_ref = nil, b_hint = 0, fs_hint = 0, mv_hint = 0, md_hint = 0, score = 0, upd = 0,
        last_move_yaw = nil, last_move_t = 0, moving = false, speed = 0,
        -- lag compensation
        lc = false, lc_t = -1e9, last_origin = nil,
        -- learning
        side = 1, conf = 0.3, pred_side = 1, brute_idx = 1, manual = false,
        shots = 0, hits = 0, misses = 0, kills = 0, hit_streak = 0, miss_streak = 0,
        last_shot_t = -1e9, reveal_t = -1e9, last_reason = nil,
        prev_result = nil, hit_side = 0, ab_score = 0, ab_flips = 0, preflipped = false,
        -- output
        at_target = 0, raw_yaw = 0, raw_pitch = 0, amount = 0,
        resolved_yaw = 0, resolved_pitch = 0, resolved = false, applied = false,
        -- bookkeeping
        sim_time = nil, last_tick = -1, seen_rt = -1e9, pawn = nil, pawn_addr = nil, en_eye = nil,
        node = nil, node_addr = nil, mem_written = false,
    }
    local saved = (is_sid and CFG.persist) and RES.store[key] or nil
    if type(saved) == "table" then
        rec.side   = (saved.side == -1) and -1 or 1
        rec.conf   = clamp((tonumber(saved.conf) or 0) * 0.6, 0, 0.6)
        rec.hits   = tonumber(saved.hits) or 0
        rec.misses = tonumber(saved.misses) or 0
    end
    return rec
end

function RES.get_record(ctrl, pawn, addr)
    local key, is_sid = RES.player_key(ctrl, pawn)
    if not key then return nil end
    local rec = RES.records[key]
    if not rec then
        rec = RES.extend(RES.new_record(key, is_sid))
        rec.name = (ctrl and safe(ctrl.name, ctrl)) or safe(pawn.name, pawn) or "?"
        RES.records[key] = rec
    end
    if rec.pawn_addr ~= addr then
        if rec.pawn_addr and RES.by_pawn[rec.pawn_addr] == rec then RES.by_pawn[rec.pawn_addr] = nil end
        rec.pawn_addr = addr
        RES.by_pawn[addr] = rec
    end
    rec.pawn = pawn
    return rec
end

function RES.record_by_pawn(pawn)
    if not pawn then return nil end
    local addr = safe(pawn.address, pawn)
    return addr and RES.by_pawn[addr] or nil
end

function RES.record_by_controller(ctrl)
    if not ctrl then return nil end
    local key = RES.player_key(ctrl, nil)
    local rec = key and RES.records[key] or nil
    return rec or RES.record_by_pawn(safe(ctrl.pawn, ctrl))
end

function RES.remember(rec)
    if not rec.is_sid then return end
    RES.store[rec.key] = { side = rec.side, conf = rec.conf, hits = rec.hits, misses = rec.misses, t = os.time() }
    RES.store_dirty = true
end

function RES.store_load()
    local data, store = safe(db.load, META.db, {}), {}
    if type(data) == "table" then
        for k, v in pairs(data) do              -- the file is user-editable: keep well-formed entries only
            if type(k) == "string" and #k <= 32 and type(v) == "table" then
                store[k] = { side = (v.side == -1) and -1 or 1, conf = clamp(tonumber(v.conf) or 0, 0, 1),
                             hits = max(0, floor(tonumber(v.hits) or 0)), misses = max(0, floor(tonumber(v.misses) or 0)),
                             t = tonumber(v.t) or 0 }
            end
        end
    end
    RES.store = store
end

function RES.store_save(force)
    if not CFG.persist or (not RES.store_dirty and not force) then return end
    local list = {}
    for k, v in pairs(RES.store) do
        if type(v) == "table" then list[#list + 1] = { k = k, t = tonumber(v.t) or 0 }
        else RES.store[k] = nil end
    end
    if #list > C.DB_MAX then
        tsort(list, function(a, b) return a.t > b.t end)
        for i = C.DB_MAX + 1, #list do RES.store[list[i].k] = nil end
    end
    if safe(db.save, META.db, RES.store) == true then RES.store_dirty = false end
end

-- ---------------------------------------------------------------- history + classification
function RES.push_history(rec, yaw, pitch)
    local H = C.HISTORY
    if rec.n > 0 then
        local prev_yaw, prev_pitch = rec.yaws[rec.head], rec.pitches[rec.head]
        rec.dhead = rec.dhead % H + 1
        rec.deltas[rec.dhead] = normalize(yaw - prev_yaw)
        rec.dn = min(H, rec.dn + 1)
        if abs(pitch - prev_pitch) > 45 then
            rec.pitch_jit = min(6, rec.pitch_jit + 1)
        else
            rec.pitch_jit = max(0, rec.pitch_jit - 0.5)
        end
        rec.p_avg = lerp(rec.p_avg, pitch, 0.3)
    else
        rec.p_avg = pitch
    end
    rec.head = rec.head % H + 1
    rec.yaws[rec.head] = yaw
    rec.pitches[rec.head] = pitch
    rec.n = min(H, rec.n + 1)
end

function RES.circular_mean(rec)
    local sx, sy = 0, 0
    for i = 1, rec.n do
        local a = rad(rec.yaws[i])
        sx, sy = sx + cos(a), sy + sin(a)
    end
    if abs(sx) < 1e-6 and abs(sy) < 1e-6 then return rec.yaws[rec.head] end
    return normalize(deg(atan2(sy, sx)))
end

-- RES.jitter_model (two-cluster model) lives in the 4.2 additions below.
-- static / sway / jitter / spin / random from the delta window, plus a pitch class.
function RES.classify(rec)
    local dn = rec.dn
    if dn < 3 then
        rec.mode, rec.mode_conf = "static", 0
        return
    end
    local H, JMD = C.HISTORY, C.JITTER_MIN_DELTA
    local old_mode = rec.mode
    local small_sum, small_n = 0, 0
    local sum_abs, sum_signed, flips, big, prev_sign, alt, pairs_n = 0, 0, 0, 0, 0, 0, 0
    local prev_d
    local idx = (dn == H) and (rec.dhead % H + 1) or 1      -- oldest delta first
    local deltas = rec.deltas
    for _ = 1, dn do
        local d = deltas[idx]
        local ad = abs(d)
        sum_abs, sum_signed = sum_abs + ad, sum_signed + d
        if ad > JMD then
            big = big + 1
            local s = (d > 0) and 1 or -1
            if prev_sign ~= 0 and s ~= prev_sign then flips = flips + 1 end
            prev_sign = s
        else
            small_sum, small_n = small_sum + ad, small_n + 1
        end
        if prev_d then
            pairs_n = pairs_n + 1
            local m = max(ad, abs(prev_d))
            -- two consecutive deltas of equal size and opposite sign = two-way jitter
            if m > JMD * 0.5 and abs(d + prev_d) < max(4, 0.35 * m) then alt = alt + 1 end
        end
        prev_d = d
        idx = idx % H + 1
    end

    local mean_abs, mean_signed = sum_abs / dn, sum_signed / dn
    rec.mean_abs = mean_abs
    rec.jit_alt = (pairs_n > 0) and (alt / pairs_n) or 0

    if abs(mean_signed) > C.SPIN_MIN_RATE and big >= dn * 0.6 and flips <= 1 then
        rec.mode, rec.spin_rate, rec.mode_conf = "spin", mean_signed, min(1, big / dn)
    elseif (big >= dn * 0.4 and flips >= max(2, floor(big * 0.5)))
        -- delayed jitter: few big deltas, every one of them reverses the previous, quiet in between
        or (big >= 3 and flips >= big - 1 and (small_n == 0 or small_sum / small_n < 4)) then
        rec.mode = "jitter"
        rec.center = RES.circular_mean(rec)
        local amp = 0
        for i = 1, rec.n do amp = amp + abs(normalize(rec.yaws[i] - rec.center)) end
        rec.amp = amp / rec.n
        rec.mode_conf = min(1, (flips / max(1, big - 1)) * 0.5 + max(rec.jit_alt, 0.5) * 0.5)
        RES.jitter_model(rec)
    elseif mean_abs < C.STATIC_MAX_DELTA then
        rec.mode, rec.mode_conf = "static", 1 - mean_abs / C.STATIC_MAX_DELTA
    elseif mean_abs < C.SWAY_MAX_DELTA then
        rec.mode, rec.center, rec.mode_conf = "sway", RES.circular_mean(rec), 0.7
    else
        rec.mode, rec.center, rec.mode_conf = "random", RES.circular_mean(rec), 0.5
    end

    -- Hysteresis: a new class has to repeat before it replaces the current one.
    if rec.mode ~= old_mode and dn >= 6 then
        if rec.mode_cand == rec.mode then rec.mode_cnt = rec.mode_cnt + 1
        else rec.mode_cand, rec.mode_cnt = rec.mode, 1 end
        if rec.mode_cnt < C.MODE_CONFIRM then rec.mode = old_mode end
    else
        rec.mode_cand, rec.mode_cnt = nil, 0
    end
    if rec.mode ~= "jitter" then rec.jit_pconf = 0 end

    if rec.pitch_jit >= 3 then rec.pitch_kind = "FLICK"
    elseif rec.p_avg >= 80 then rec.pitch_kind = "DOWN"
    elseif rec.p_avg <= -80 then rec.pitch_kind = "UP"
    elseif abs(rec.p_avg) < 3 and rec.mode ~= "static" then rec.pitch_kind = "ZERO"
    else rec.pitch_kind = "" end
end

-- ---------------------------------------------------------------- hints
local function hb_kind(h)
    local g = h.group
    if g == 4 then return "la" elseif g == 5 then return "ra"
    elseif g == 6 then return "ll" elseif g == 7 then return "rl" end
    local n = h.group_name
    if type(n) == "string" then
        n = s_lower(n)
        local left = s_find(n, "left", 1, true) ~= nil
        local right = s_find(n, "right", 1, true) ~= nil
        if s_find(n, "arm", 1, true) then
            if left then return "la" elseif right then return "ra" end
        elseif s_find(n, "leg", 1, true) then
            if left then return "ll" elseif right then return "rl" end
        end
    end
    return nil
end

-- Body yaw from a left/right hitbox pair (highest hitbox of each group).
local function pair_yaw(hbs, lk, rk)
    local L, R
    for i = 1, #hbs do
        local h = hbs[i]
        local c = type(h) == "table" and h.center or nil
        if c then
            local k = hb_kind(h)
            if k == lk then
                if not L or c.z > L.z then L = c end
            elseif k == rk then
                if not R or c.z > R.z then R = c end
            end
        end
    end
    if not L or not R then return nil end
    local dx, dy = L.x - R.x, L.y - R.y
    if dx * dx + dy * dy < 4 then return nil end
    return normalize(deg(atan2(dy, dx)) - 90)   -- (L - R) is the body's left vector
end

-- Model yaw. Primary: the scene node rotation of the pawn (one cached node wrapper and one
-- vector read per update, no hitbox tables). Fallback: hitbox geometry every BODY_EVERY updates.
local function read_node_yaw(node, field)
    return node:get("CGameSceneNode", field, "vector").y
end

local function wrap_ptr(ptr)
    if type(ptr) ~= "number" or ptr == 0 then return nil end
    local ok, ent = pcall(entity.from_address, ptr)
    if ok and ent then return ent end
    return nil
end

-- Scene node wrapper for a pawn. CS2 path: C_BaseEntity.m_CBodyComponent -> CBodyComponent.m_pSceneNode.
-- The flat C_BaseEntity.m_pGameSceneNode is kept as a fallback for builds that still expose it.
function RES.node_entity(pawn)
    local ok, ptr = pcall(pawn.get, pawn, "C_BaseEntity", "m_CBodyComponent", "ptr")
    if ok then
        local body = wrap_ptr(ptr)
        if body then
            local ok2, node_ptr = pcall(body.get, body, "CBodyComponent", "m_pSceneNode", "ptr")
            if ok2 then
                local node = wrap_ptr(node_ptr)
                if node then return node end
            end
        end
    end
    local ok3, flat = pcall(pawn.get, pawn, "C_BaseEntity", "m_pGameSceneNode", "ptr")
    if ok3 then return wrap_ptr(flat) end
    return nil
end

function RES.node_fail()
    RES.node_bad = RES.node_bad + 1
    if (RES.node_bad >= C.NODE_FAILS and RES.node_good == 0) or RES.node_bad >= 4 * C.NODE_FAILS then
        RES.node_ok = false
        say("scene node rotation unavailable: the body hint falls back to hitboxes")
    end
    return nil
end

function RES.node_yaw(rec, pawn)
    if not RES.node_ok then return nil end
    -- entity.from_address is documented for insecure scenarios only.
    if not RES.insecure then return nil end
    local node = rec.node
    if node == nil or rec.node_addr ~= rec.pawn_addr then
        node = RES.node_entity(pawn)
        if not node then return RES.node_fail() end
        rec.node, rec.node_addr = node, rec.pawn_addr
    end
    local ok, y
    local f = RES.node_field
    if f then
        ok, y = pcall(read_node_yaw, node, f)
    else
        for i = 1, #NODE_FIELDS do
            ok, y = pcall(read_node_yaw, node, NODE_FIELDS[i])
            if ok and type(y) == "number" then RES.node_field = NODE_FIELDS[i] break end
        end
    end
    if not ok or type(y) ~= "number" or y ~= y then
        rec.node = nil
        return RES.node_fail()
    end
    RES.node_good, RES.node_bad = RES.node_good + 1, 0
    return normalize(y)
end

-- The delta to the CURRENT eye yaw is recomputed every update so the reference stays valid
-- under jitter.
function RES.body_hint(rec, pawn, yaw, refresh)
    if not RES.body_ok then return 0 end
    local ref = RES.node_yaw(rec, pawn)
    if ref then
        rec.body_ref = ref
    elseif refresh or rec.body_ref == nil then
        local hbs = safe(pawn.hitboxes, pawn)
        if type(hbs) ~= "table" then
            RES.body_bad = RES.body_bad + 1
            if RES.body_bad > 40 and RES.body_good == 0 then RES.body_ok = false end
            return 0
        end
        rec.body_ref = pair_yaw(hbs, "ll", "rl") or pair_yaw(hbs, "la", "ra")
    end
    ref = rec.body_ref
    if not ref then return 0 end
    local d = normalize(ref - yaw)
    if abs(d) > C.BODY_SANE_DELTA then
        RES.body_bad = RES.body_bad + 1
        if RES.body_bad > 40 and RES.body_good < RES.body_bad / 8 then
            RES.body_ok = false
            notify("Body yaw hint disabled (model yaw data not usable)")
        end
        return 0
    end
    RES.body_good = RES.body_good + 1
    rec.body_delta = d
    if abs(d) < C.BODY_MIN_DELTA then return 0 end
    return clamp(d / C.BODY_MAX_DELTA, -1, 1)
end

-- Which side of the enemy head is covered from our point of view.
-- Side +1 (CCW) moves the head toward OUR right, so right cover => +1.
function RES.freestand_hint(lp, pawn, lp_eye, en_eye)
    local yaw = rad(U.yaw_to(lp_eye, en_eye))
    local rx, ry = sin(yaw) * C.FS_OFFSET, -cos(yaw) * C.FS_OFFSET
    RES.fs_skip[1], RES.fs_skip[2] = lp, pawn
    local tl = safe(trace.line, lp_eye, vector(en_eye.x - rx, en_eye.y - ry, en_eye.z), RES.fs_opts)
    local tr = safe(trace.line, lp_eye, vector(en_eye.x + rx, en_eye.y + ry, en_eye.z), RES.fs_opts)
    RES.fs_skip[1], RES.fs_skip[2] = nil, nil
    if type(tl) ~= "table" or type(tr) ~= "table" then return 0 end
    local bl, br = (tonumber(tl.fraction) or 1) < 0.98, (tonumber(tr.fraction) or 1) < 0.98
    if bl == br then return 0 end
    return br and 1 or -1
end

function RES.movement_hint(rec, yaw, now)
    if rec.moving or not rec.last_move_yaw then return 0 end
    local age = now - rec.last_move_t
    if age < 0 or age > C.MOVE_MEM_TIME then return 0 end
    local d = normalize(rec.last_move_yaw - yaw)
    if abs(d) < 20 then return 0 end
    return sign(d) * (1 - age / C.MOVE_MEM_TIME)
end

-- ---------------------------------------------------------------- decision
function RES.brute_len()
    return (CFG.brute_pat == E.PAT_STEP) and #STEP_SEQ or #BRUTE
end

-- Multiplier and absolute amount for a brute index (defaults to the record's current index).
function RES.brute_entry(rec, idx)
    local m = CFG.mode
    if m == E.MODE_STATIC or m == E.MODE_OFFSET then return 1, CFG.desync end
    idx = idx or rec.brute_idx
    if CFG.brute_pat == E.PAT_STEP then
        local i = (idx - 1) % #STEP_SEQ + 1
        return STEP_SEQ[i], STEP_SEQ[i] * CFG.brute_step
    end
    local i = (idx - 1) % #BRUTE + 1
    return BRUTE[i], BRUTE[i] * CFG.desync
end

function RES.decide_side(rec, b, fs, mv, md)
    rec.b_hint, rec.fs_hint, rec.mv_hint, rec.md_hint = b, fs, mv, md
    if rec.manual or CFG.mode == E.MODE_BRUTE or CFG.mode == E.MODE_OFFSET then
        rec.score, rec.pred_side = rec.side, rec.side
        return
    end
    local score = rec.side * rec.conf * C.W_LEARNED + RES.class_bias(rec)
    local hw, hs = RES.hw, RES.hsign
    if CFG.body then score = score + b * hs.b * C.W_BODY * hw.b end
    if CFG.freestand then score = score + fs * hs.fs * C.W_FREESTAND * hw.fs end
    if CFG.move_mem then score = score + mv * hs.mv * C.W_MOVE * hw.mv end
    if CFG.move_dir then score = score + md * hs.md * C.W_MOVEDIR * hw.md end
    rec.score = score
    if abs(score) >= C.SIDE_DEADZONE then
        rec.pred_side = (score > 0) and 1 or -1
    end
end

function RES.resolve_pitch(rec, pitch)
    local pm = CFG.pitch
    if pm == E.PITCH_OFF then return pitch end
    if pm == E.PITCH_CLAMP then return clamp(pitch, -89, 89) end
    if pm == E.PITCH_DOWN then return 89 end
    if pm == E.PITCH_ZERO then return 0 end
    if pm == E.PITCH_UP then return -89 end
    if pitch > 89.5 then return 89 end
    if pitch < -89.5 then return -89 end
    if rec.pitch_jit >= 3 then return 89 end          -- fake-pitch flicker: assume looking down
    return clamp(pitch, -89, 89)
end

function RES.compute(rec, yaw, pitch)
    local mode, m = rec.mode, CFG.mode
    local at = rec.at_target

    if m == E.MODE_OFFSET then
        rec.amount = CFG.yaw_off
        rec.resolved_yaw = normalize(at + CFG.yaw_off)
        rec.resolved_pitch = RES.resolve_pitch(rec, pitch)
        rec.resolved = true
        return
    end

    rec.jit_k = nil
    if mode == "jitter" and (m == E.MODE_ADAPTIVE or m == E.MODE_JITSPIN) then
        local jm = CFG.jit_mode
        if jm == E.JIT_FOLLOW then
            rec.amount, rec.resolved_yaw = 0, yaw
            rec.resolved_pitch = RES.resolve_pitch(rec, pitch)
            rec.resolved = true
            return
        end
        if rec.jit_pconf >= C.JIT_PRED_CONF and rec.jit_half > 0 then
            local seq = JIT_SEQ[(jm == E.JIT_PREDICT) and 2 or 1]
            local k = seq[(rec.brute_idx - 1) % #seq + 1]
            -- the newest side has lasted a full period: the next update is on the other side
            local nxt = (rec.jit_run >= rec.jit_period) and -rec.jit_side or rec.jit_side
            local off = nxt * rec.jit_half * k
            rec.jit_k, rec.amount = k, off
            rec.resolved_yaw = normalize(rec.center + off)
            rec.resolved_pitch = RES.resolve_pitch(rec, pitch)
            rec.resolved = true
            return
        end
    end

    local base
    if CFG.base == E.BASE_TARGET then
        base = at
    elseif CFG.base == E.BASE_EYE then
        base = yaw
    elseif mode == "spin" then
        base = at
    elseif mode == "jitter" or mode == "sway" then
        base = rec.center
    elseif mode == "random" and rec.mean_abs > C.RANDOM_CENTER_AT then
        base = rec.center
    else
        base = yaw
    end
    if m == E.MODE_JITSPIN then
        if mode == "spin" then
            base = normalize(yaw + rec.spin_rate * C.SPIN_LEAD)
        elseif mode == "jitter" then
            base = rec.center
        end
    end

    local _, amount = RES.brute_entry(rec)
    if mode == "jitter" then
        amount = amount * CFG.jit_sc_f
    elseif mode == "random" then
        amount = amount * 0.75
    elseif mode == "spin" and m == E.MODE_JITSPIN then
        amount = amount * 0.5
    end
    if rec.moving then amount = amount * CFG.move_sc_f end
    if CFG.face_damp and (mode == "static" or mode == "sway") and abs(normalize(yaw - at)) < C.FACE_ANGLE then
        amount = amount * C.FACE_SCALE
    end

    rec.amount = amount
    rec.resolved_yaw = normalize(base + rec.pred_side * amount)
    rec.resolved_pitch = RES.resolve_pitch(rec, pitch)
    rec.resolved = true
end

-- Little trust in the current guess: the ragebot assist prefers the body and adjusts hitchance.
-- Returns false or a reason tag ("LC" / "RES").
function RES.unresolved(rec)
    if not rec or not rec.resolved then return false end
    if rec.lc then return "LC" end
    if rec.manual then return false end
    if rec.miss_streak >= 2 or rec.brute_idx >= 3 then return "RES" end
    if rec.mode == "random" and rec.conf < 0.5 then return "RES" end
    if rec.mode == "jitter" and rec.amp > 35 and rec.conf < 0.5 then return "RES" end
    return false
end

-- ---------------------------------------------------------------- delivery of the resolved yaw
-- Channel 1 (default): RES.cmd_fix corrects the command the ragebot fires with.
-- Channel 2 (optional, Allow Insecure): the resolved angles are written into m_angEyeAngles.
function RES.can_write()
    return CFG.mem_write == true and RES.insecure and RES.write_ok ~= false
end

function RES.apply(pawn, rec)
    rec.applied, rec.mem_written = false, false
    if not rec.resolved then return end
    if not RES.can_write() then
        rec.applied = CFG.cmd_fix == true            -- delivered through the createmove channel
        return
    end
    local ang = vector(rec.resolved_pitch, rec.resolved_yaw, 0)

    if RES.write_cls then
        local ok, res = pcall(pawn.set, pawn, RES.write_cls, "m_angEyeAngles", "vector", ang)
        if ok and res ~= false then
            rec.applied, rec.mem_written = true, true
            RES.write_fails = 0
        else
            RES.write_fails = RES.write_fails + 1
            if RES.write_fails > 20 then
                RES.write_ok = false
                notify("Eye angle write failing; the createmove channel stays active")
            end
        end
        return
    end

    for i = 1, #EYE_CLASSES do
        local ok, res = pcall(pawn.set, pawn, EYE_CLASSES[i], "m_angEyeAngles", "vector", ang)
        if ok and res ~= false then
            RES.write_cls, RES.write_ok, rec.applied, rec.mem_written = EYE_CLASSES[i], true, true, true
            return
        end
    end
    RES.write_ok = false
    notify("m_angEyeAngles not writable (schema / insecure); the createmove channel stays active")
end

function RES.read_simtime(pawn)
    if not RES.simtime_ok then return nil end
    local ok, v = pcall(pawn.get, pawn, "C_BaseEntity", "m_flSimulationTime", "float")
    if ok and type(v) == "number" then return v end
    RES.simtime_ok = false
    return nil
end

-- ---------------------------------------------------------------- per-player update
function RES.process(pawn, ctrl, addr, lp, lp_alive, lp_eye, now, tick, rt)
    local rec = RES.get_record(ctrl, pawn, addr)
    if not rec then return nil end
    local gap = rt - rec.seen_rt                 -- > 0.25 s: dormant / respawned in between
    rec.seen_rt = rt

    local eye = safe(pawn.eye_angles, pawn)
    if not eye then return rec end
    local yaw, pitch = normalize(eye.y), eye.x

    -- Freshness gate: only analyse genuinely new network data.
    local simt = RES.read_simtime(pawn)
    local fresh
    if simt then
        if CFG.lc_detect and rec.sim_time and gap < 0.25 and simt < rec.sim_time - 1e-4 then
            rec.lc_t = now                       -- simulation time went backwards: tickbase shift
        end
        fresh = (simt ~= rec.sim_time)
        rec.sim_time = simt
    else
        fresh = (tick ~= rec.last_tick)
        -- Echo guard: without simulation time we could read back our own write.
        if fresh and rec.mem_written
            and abs(normalize(yaw - rec.resolved_yaw)) < 0.01
            and abs(pitch - rec.resolved_pitch) < 0.01 then
            fresh = false
        end
    end
    rec.last_tick = tick

    -- The LC flag must expire even while no fresh data arrives (dormant / frozen target).
    local lc_age = now - rec.lc_t
    rec.lc = CFG.lc_detect and lc_age >= 0 and lc_age < C.LC_HOLD
    -- A sample right after the enemy fired carries his aim yaw, not his anti-aim. A negative
    -- age means the clock was reset: the stamp is stale and must not freeze the record.
    local reveal_age = now - rec.reveal_t
    if not fresh or (reveal_age >= 0 and reveal_age < C.REVEAL_TIME) then
        if rec.resolved then RES.apply(pawn, rec) end
        return rec
    end
    if gap > 0.25 then
        rec.n, rec.dn, rec.head, rec.dhead = 0, 0, 0, 0       -- stale history must not mix in
        rec.last_origin, rec.body_ref, rec.fs_cache, rec.node = nil, nil, nil, nil
        rec.pitch_jit, rec.jit_pconf, rec.mode_cand, rec.mode_cnt = 0, 0, nil, 0
    end
    rec.upd = rec.upd + 1

    local origin = safe(pawn.origin, pawn)
    if CFG.lc_detect and origin and rec.last_origin then
        local dx, dy, dz = origin.x - rec.last_origin.x, origin.y - rec.last_origin.y, origin.z - rec.last_origin.z
        if dx * dx + dy * dy + dz * dz > C.LC_DIST_SQR then rec.lc_t = now end
    end
    rec.last_origin = origin
    rec.lc = CFG.lc_detect and (now - rec.lc_t) < C.LC_HOLD and (now - rec.lc_t) >= 0
    -- Angles received right after an LC break are not his anti-aim: keep the last stable result.
    if rec.lc and CFG.lc_hold and rec.resolved and (now - rec.lc_t) < C.LC_FREEZE then
        RES.apply(pawn, rec)
        return rec
    end

    local vel = safe(pawn.velocity, pawn)
    if not vel then return rec end
    local speed = vel:length2d()
    rec.raw_yaw, rec.raw_pitch, rec.speed = yaw, pitch, speed
    RES.push_history(rec, yaw, pitch)
    RES.classify(rec)

    if speed > C.MOVE_SPEED then
        rec.moving = true
        rec.last_move_yaw = normalize(deg(atan2(vel.y, vel.x)))
        rec.last_move_t = now
    else
        rec.moving = false
    end

    local en_eye = safe(pawn.eye_position, pawn)
    if not en_eye then
        rec.resolved, rec.applied = false, false   -- do not deliver a stale yaw
        return rec
    end
    rec.en_eye = en_eye
    rec.at_target = normalize(U.yaw_to(en_eye, lp_eye))

    local b = CFG.body and RES.body_hint(rec, pawn, yaw, rec.upd % C.BODY_EVERY == 0) or 0
    local fs = 0
    if CFG.freestand and lp_alive then
        if rec.fs_cache == nil or rec.upd % C.FS_EVERY == 1 then
            rec.fs_cache = RES.freestand_hint(lp, pawn, lp_eye, en_eye)
        end
        fs = rec.fs_cache or 0
    end
    local mv = CFG.move_mem and RES.movement_hint(rec, yaw, now) or 0
    local md = 0
    if CFG.move_dir and speed > C.MOVEDIR_SPEED and rec.last_move_yaw then
        md = sign(normalize(rec.last_move_yaw - rec.at_target))
    end

    RES.decide_side(rec, b, fs, mv, md)
    RES.compute(rec, yaw, pitch)
    RES.apply(pawn, rec)
    return rec
end

-- ---------------------------------------------------------------- shot feedback
function RES.log(kind, text)
    X.feed(kind, text)
    if CFG.log_hits then say(text) end
end

-- Spread cone sample, refreshed every createmove. At weapon_fire the smaller of the last two
-- samples is used: at least one of them predates the shot's own accuracy penalty.
function RES.sample_spread(lp)
    if not (CFG.enable and CFG.feedback and CFG.spread_blame) then
        STATE.inacc, STATE.inacc_prev = nil, nil
        return
    end
    local info = get_weapon_info(lp)
    local v = nil
    if type(info) == "table" then
        local ia, sp = tonumber(info.inaccuracy), tonumber(info.spread)
        if ia and sp and ia >= 0 and sp >= 0 and ia + sp < 1 then v = ia + sp end
    end
    STATE.inacc_prev, STATE.inacc = STATE.inacc, v
end

function RES.is_local_controller(ctrl)
    if not ctrl then return false end
    local lc = entity.local_controller()
    if not lc then return false end
    return safe(ctrl.address, ctrl) == safe(lc.address, lc)
end

-- Target of our shot. Returns record, on_target (the shot ray really crossed a model).
-- The angles the ragebot aimed with (before the resolver correction) are tried first: they
-- were aimed at the model the client draws.
function RES.find_shot_target(lp)
    local from = safe(lp.eye_position, lp)
    if not from then return nil, false end
    local angs, n = {}, 0
    if STATE.raw_y then n = n + 1 angs[n] = vector(STATE.raw_p, STATE.raw_y, 0) end
    if STATE.cmd_y and STATE.cmd_y ~= STATE.raw_y then n = n + 1 angs[n] = vector(STATE.cmd_p, STATE.cmd_y, 0) end
    local view = safe(engine.view_angles)
    if view then n = n + 1 angs[n] = view end
    for i = 1, n do
        local r = safe(trace.bullet, from, from + angs[i]:forward() * 8192)
        if type(r) == "table" and r.hit and r.entity then
            local rec = RES.record_by_pawn(r.entity)
            if rec then return rec, true end
        end
    end
    -- the ray crossed no model: the shot is off target, the record is only the best guess
    if RB.t_addr then
        local rec = RES.by_pawn[RB.t_addr]
        if rec then return rec, false end
    end
    local va = angs[1]
    if not va then return nil, false end
    local best, best_fov = nil, 12
    local rt = globals.realtime()
    for _, rec in pairs(RES.records) do
        if rec.en_eye and rt - rec.seen_rt < 0.2 then
            local fov = U.fov(from, rec.en_eye, va)
            if fov < best_fov then best, best_fov = rec, fov end
        end
    end
    return best, false
end

function RES.on_weapon_fire(ev)
    if not CFG.enable then return end
    local ctrl = safe(ev.get_controller, ev, "userid")
    if not ctrl then return end
    if not RES.is_local_controller(ctrl) then
        local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "userid")) or RES.record_by_controller(ctrl)
        if rec then rec.reveal_t = globals.curtime() end
        return
    end
    if not CFG.feedback then return end
    if WPN.non_gun_name(safe(ev.get_string, ev, "weapon")) then return end
    local lp = entity.local_pawn()
    if not lp then return end
    local info = get_weapon_info(lp)
    if type(info) == "table" and info.gun == false then return end

    local rec, on_target = RES.find_shot_target(lp)
    if not rec then return end
    local now = globals.curtime()
    if now - rec.last_shot_t < C.SHOT_DEDUPE then return end   -- spray: one pending shot per slice
    rec.last_shot_t = now
    rec.shots = rec.shots + 1
    RES.stats.shots = RES.stats.shots + 1

    local cone = nil
    local a, b = STATE.inacc, STATE.inacc_prev
    local s = (a and b) and min(a, b) or a or b
    if s and rec.en_eye then
        local from = safe(lp.eye_position, lp)
        if from then cone = s * from:dist(rec.en_eye) end
    end
    local pending = RES.pending
    pending[#pending + 1] = {
        key = rec.key, t = now, side = rec.pred_side, idx = rec.brute_idx, mode = rec.mode,
        moving = rec.moving, lp_air = STATE.lp_air, baim = RB.baim ~= nil, lc = rec.lc,
        cone = cone, on_target = on_target, jit = rec.jit_k ~= nil, ack_hit = false,
        h = { b = sign(rec.b_hint), fs = sign(rec.fs_hint), mv = sign(rec.mv_hint), md = sign(rec.md_hint) },
    }
    if #pending > C.PENDING_MAX then tremove(pending, 1) end
end

-- Oldest pending shot of this target. A pending shot attributed to another player is never
-- consumed here: the miss window / aim_ack must resolve it on its own.
function RES.take_pending(key)
    local pending = RES.pending
    for i = 1, #pending do
        if pending[i].key == key then return tremove(pending, i) end
    end
    return nil
end

-- Hints that agreed with the confirmed side gain weight, the others lose it. w scales the
-- step (soft misses learn with half weight). A hint whose weight reaches the floor has an
-- inverted sign: it is flipped ONCE and restarts at neutral weight instead of being disabled.
function RES.learn_hints(shot, truth, w)
    if not CFG.hint_learn or not shot or not shot.h or truth == 0 then return end
    w = w or 1
    local hw, hs, fl = RES.hw, RES.hsign, RES.flipped
    for k, v in pairs(shot.h) do
        if v ~= 0 then
            if v * hs[k] == truth then
                hw[k] = min(C.HW_MAX, hw[k] + C.HW_GAIN * w)
            else
                hw[k] = max(C.HW_MIN, hw[k] - C.HW_LOSS * w)
                if hw[k] <= C.HW_MIN + 1e-6 and not fl[k] then
                    fl[k], hs[k], hw[k] = true, -hs[k], 1
                    say("hint '" .. k .. "' kept missing: sign flipped (one time)")
                end
            end
        end
    end
end

function RES.reset_signs()
    for k in pairs(RES.hw) do RES.hw[k], RES.hsign[k], RES.flipped[k] = 1, 1, false end
end

function RES.on_hit(rec, hitgroup, dmg, given)
    local shot = given or RES.take_pending(rec.key)
    local known = shot ~= nil                       -- a hit without a pending shot proves no side
    rec.hits, rec.hit_streak, rec.miss_streak = rec.hits + 1, rec.hit_streak + 1, 0
    local st = RES.stats
    st.hits = st.hits + 1

    local head = (hitgroup == K.HG_HEAD)
    if head then st.heads = st.heads + 1 end
    local partial = CFG.body_partial and not head and not (shot and shot.baim)
    local used_side = shot and shot.side or rec.side
    local m = known and RES.brute_entry(rec, shot.idx) or 0   -- multiplier that was live at fire time
    local jit = shot and shot.jit                              -- jitter model shot: the index that hit stays
    if known and not partial and m ~= 0 and not jit then
        rec.side = sign(used_side * m)
        if CFG.brute_pat ~= E.PAT_STEP and abs(m) == 1 then rec.brute_idx = 1 end
        RES.learn_hints(shot, rec.side)
    end

    -- anti-anti-bruteforce: a second hit in a row that only landed on the other side means he
    -- flips after every hit; a second hit on the same side means he does not.
    if known and rec.prev_result == "hit" and rec.hit_side ~= nil then
        if rec.preflipped or used_side ~= rec.hit_side then
            rec.ab_score = min(3, rec.ab_score + 1)
        else
            rec.ab_score = max(0, rec.ab_score - 1)
        end
    end
    if known then
        rec.hit_side, rec.prev_result, rec.preflipped = used_side, "hit", false
    else
        rec.hit_side, rec.prev_result, rec.preflipped = nil, "hit", false
    end
    rec.conf = min(1, rec.conf + C.HIT_CONF_GAIN * (head and 1.25 or (partial and C.PARTIAL_GAIN or 1)))

    RES.note_hit(rec, shot, known and not partial and m ~= 0 and not jit)
    local pre = ""
    if CFG.anti_ab and rec.ab_score >= 2 and not partial then
        rec.side = -rec.side                      -- he will flip after this hit: be there first
        rec.ab_flips = rec.ab_flips + 1
        rec.preflipped = true
        pre = "  · pre-flip"
    end
    rec.last_reason = nil
    RES.remember(rec)
    RES.log(head and "hit" or "body", format("%s  %s %d%s%s", rec.name, head and "HEAD" or "BODY",
        floor(tonumber(dmg) or 0), partial and " (partial)" or "", pre))
end

-- Reason of a miss. The optional aim_ack extension is authoritative when it is wired;
-- otherwise the heuristics decide. Hard: death / lost / lagcomp / local. Soft: off_target /
-- airborne / moving / spread. "resolver": everything else.
function RES.miss_reason(shot, rec, ack)
    if ack then
        local r = ACK_REASON[ack]
        if r then
            shot.src = "ack"
            return r
        end
    end
    if STATE.lp_dead then return "death" end                  -- we died before the shot could register
    if STATE.rt - rec.seen_rt > 0.25 then return "lost" end   -- target went dormant / left
    if shot.lc then return "lagcomp" end
    if shot.on_target == false then return "off_target" end   -- the ray never crossed his model
    if shot.lp_air then return "airborne" end
    if shot.moving then return "moving" end
    if CFG.spread_blame and shot.cone and shot.cone > C.SPREAD_BLAME then return "spread" end
    return "resolver"
end

function RES.on_miss(shot, rec, ack)
    local st = RES.stats
    local reason = RES.miss_reason(shot, rec, ack)
    local hard = HARD[reason] == true
    rec.misses, rec.hit_streak, rec.last_reason = rec.misses + 1, 0, reason
    st.misses = st.misses + 1
    st[reason] = (st[reason] or 0) + 1
    local src = (shot.src == "ack") and " [ack]" or ""

    if hard then
        -- not the resolver's fault: no brute step, no anti-bruteforce bookkeeping
        st.hard = st.hard + 1
        rec.conf = max(0, rec.conf - C.SOFT_CONF_LOSS)
        RES.remember(rec)
        RES.log("miss", format("%s  MISS (%s)%s", rec.name, reason, src))
        return
    end

    -- soft miss: the shot may still have been the resolver's fault, so it teaches with half weight
    local w = (reason == "resolver") and 1 or C.SOFT_W
    if w < 1 then st.soft = st.soft + 1 end
    rec.conf = max(0, rec.conf - C.MISS_CONF_LOSS * w)
    local prev = rec.prev_result
    rec.prev_result = "miss"
    rec.manual = false
    if w == 1 and prev == "hit" and CFG.anti_ab then
        if rec.preflipped then
            rec.ab_score = max(0, rec.ab_score - 1)   -- the pre-flip was wrong
            rec.preflipped = false
        elseif shot.side == rec.hit_side then
            rec.ab_score = min(3, rec.ab_score + 1)   -- same side missed right after a hit: he flipped
        end
    end
    rec.miss_streak = rec.miss_streak + w
    if not shot.jit then
        local bm = RES.brute_entry(rec, shot.idx)
        if abs(bm) == 1 then
            local wrong = sign(shot.side * bm)
            RES.learn_hints(shot, -wrong, w)                                     -- the other side was right
            RES.note_miss(rec, shot, wrong, w)
        end
    end
    local info = ""
    if rec.miss_streak >= CFG.miss_tol then
        rec.miss_streak = 0
        if CFG.mode == E.MODE_STATIC or CFG.mode == E.MODE_OFFSET then
            rec.side = -rec.side
            info = "  -> flip"
        elseif shot.idx == rec.brute_idx then            -- step once per brute index, not per queued shot
            rec.brute_idx = RES.next_brute(rec, shot)
            info = format("  -> brute %d", rec.brute_idx)
        end
    end
    RES.remember(rec)
    RES.log("miss", format("%s  MISS (%s%s)%s%s", rec.name, reason, w < 1 and " ½" or "", src, info))
end

function RES.ack_live()
    return RES.ack.n > 0 and STATE.rt - RES.ack.t < 30
end

function RES.check_pending(now)
    local pending = RES.pending
    local win = CFG.miss_win_s or 0.35
    if CFG.ack_src and RES.ack_live() then win = max(win, C.ACK_WAIT) end   -- aim_ack delivers the verdict
    for i = #pending, 1, -1 do
        local s = pending[i]
        if now - s.t > win then
            tremove(pending, i)
            local rec = RES.records[s.key]
            if rec then
                if s.ack_hit then
                    RES.on_hit(rec, s.hg, s.dmg, s)           -- aim_ack saw the hit, player_hurt never consumed it
                else
                    RES.on_miss(s, rec, nil)
                end
            end
        elseif now < s.t then
            tremove(pending, i)   -- clock went backwards (map change)
        end
    end
end

local function shot_field(shot, name) return shot[name] end

-- Optional extension (not part of doc&api.txt): if a build ever delivers the ragebot's own
-- verdict, this maps a player index to the documented controller list.
local function controller_by_target(idx)
    local players = safe(entity.players)
    if type(players) ~= "table" then return nil end
    local p = players[idx + 1] or players[idx]
    return p and p.controller or nil
end

-- events.aim_ack: the ragebot's own verdict for a shot (ragebot.Shot.result).
-- Reading an unknown field of a Shot throws, so every access goes through pcall.
function RES.on_aim_ack(shot)
    if not (CFG.enable and CFG.feedback and CFG.ack_src) then return end
    local ack = RES.ack
    ack.n, ack.t = ack.n + 1, STATE.rt
    local ok, result = pcall(shot_field, shot, "result")
    local ok2, idx = pcall(shot_field, shot, "target")
    if not ok or type(result) ~= "string" or not ok2 or type(idx) ~= "number" or idx < 0 then return end
    local ctrl = controller_by_target(idx)
    local rec = ctrl and RES.record_by_controller(ctrl) or nil
    if not rec then return end
    local pending, at = RES.pending, nil
    for i = 1, #pending do
        if pending[i].key == rec.key and not pending[i].ack_hit then at = i break end
    end
    if not at then return end
    local s = pending[at]
    if result == "hit" then
        local _, hg = pcall(shot_field, shot, "hitgroup")
        local _, dmg = pcall(shot_field, shot, "damage")
        s.ack_hit, s.hg, s.dmg = true, tonumber(hg), tonumber(dmg)   -- player_hurt normally consumes it first
        return
    end
    tremove(pending, at)
    RES.on_miss(s, rec, result)
end

function RES.on_player_hurt(ev)
    if not CFG.enable or not CFG.feedback then return end
    local lc = entity.local_controller()
    if not lc then return end
    local la = safe(lc.address, lc)
    if la == nil then return end
    local att = safe(ev.get_controller, ev, "attacker")
    local vic = safe(ev.get_controller, ev, "userid")
    local att_a = att and safe(att.address, att) or nil
    local vic_a = vic and safe(vic.address, vic) or nil
    local bullet = not WPN.non_gun_name(safe(ev.get_string, ev, "weapon"))   -- grenades / fire / knife do not teach

    if att_a == la then
        if not bullet or vic_a == la then return end
        local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "userid")) or RES.record_by_controller(vic)
        if not rec then return end
        RES.on_hit(rec, safe(ev.get_int, ev, "hitgroup") or 0, safe(ev.get_int, ev, "dmg_health") or 0)
    elseif CFG.flip_on_hurt and bullet and att and vic_a == la then
        local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "attacker")) or RES.record_by_controller(att)
        if rec then
            rec.side = -rec.side
            RES.remember(rec)
        end
    end
end

function RES.reset_history(rec)
    rec.n, rec.dn, rec.head, rec.dhead = 0, 0, 0, 0
    rec.pitch_jit, rec.pitch_kind = 0, ""
    rec.mode, rec.mode_conf = "static", 0
    rec.jit_pconf, rec.jit_k, rec.mode_cand, rec.mode_cnt = 0, nil, nil, 0
    rec.resolved, rec.applied, rec.manual = false, false, false
    rec.sim_time, rec.last_move_yaw, rec.last_origin = nil, nil, nil
    rec.body_ref, rec.fs_cache, rec.lc, rec.lc_t, rec.node = nil, nil, false, -1e9, nil
    rec.miss_streak = 0
    -- per-life anti-bruteforce state must not leak into the next spawn
    rec.prev_result, rec.hit_side, rec.preflipped, rec.ab_score = nil, nil, false, 0
    rec.en_eye, rec.at_target = nil, 0
    if rec.tried then
        for k in pairs(rec.tried) do rec.tried[k] = nil end
    end
end

function RES.on_player_death(ev)
    if not CFG.enable then return end
    local rec = RES.record_by_pawn(safe(ev.get_pawn, ev, "userid"))
        or RES.record_by_controller(safe(ev.get_controller, ev, "userid"))
    if not rec then return end
    local pending = RES.pending
    for i = #pending, 1, -1 do
        if pending[i].key == rec.key then tremove(pending, i) end
    end
    RES.reset_history(rec)
    if RES.focus == rec then RES.focus = nil end
    local att = safe(ev.get_controller, ev, "attacker")
    if att and RES.is_local_controller(att) then
        rec.kills = rec.kills + 1
        RES.log("kill", format("%s  KILL  (%d/%d)", rec.name, rec.hits, rec.misses))
    end
end

-- Manual override: rising edge of the flip bind inverts the crosshair target's side.
function RES.check_flip()
    local on = bind_on(UI.k_flip)
    if on == STATE.flip_prev then return end
    STATE.flip_prev = on
    if not on then return end
    local rec = RES.focus
    if not rec then return end
    rec.side = -rec.pred_side
    rec.pred_side = rec.side
    rec.conf = max(rec.conf, 0.6)
    rec.manual, rec.brute_idx, rec.miss_streak = true, 1, 0
    RES.remember(rec)
    RES.log("info", format("%s  manual flip -> %s", rec.name, rec.side > 0 and "L" or "R"))
end

-- ---------------------------------------------------------------- frame stage
-- After lag compensation the game may restore the networked angles: write them again.
-- Fresh pawns are fetched every time (never a cached pointer); skipped entirely if no write is possible.
function RES.reapply_all()
    if not RES.can_write() then return end
    local players = safe(entity.players)
    if type(players) ~= "table" then return end
    for i = 1, #players do
        local pawn = players[i].pawn
        if pawn then
            local addr = safe(pawn.address, pawn)
            local rec = addr and RES.by_pawn[addr] or nil
            if rec and rec.resolved and safe(pawn.alive, pawn) == true then RES.apply(pawn, rec) end
        end
    end
end

function RES.purge(rt)
    if rt - RES.last_purge < 5 then return end
    RES.last_purge = rt
    for key, rec in pairs(RES.records) do
        if rt - rec.seen_rt > C.PURGE_AFTER then
            if rec.pawn_addr and RES.by_pawn[rec.pawn_addr] == rec then RES.by_pawn[rec.pawn_addr] = nil end
            if RES.focus == rec then RES.focus = nil end
            RES.records[key] = nil
        end
    end
end

function RES.frame(st)
    if st ~= E.STAGE_NET_END and st ~= E.STAGE_LAGCOMP then return end
    if not CFG.enable or not engine.in_game() then
        RES.focus = nil
        return
    end
    if st == E.STAGE_LAGCOMP then
        RES.reapply_all()
        return
    end
    RES.insecure = safe(client.insecure) == true
    STATE.insecure = RES.insecure

    local lp = entity.local_pawn()
    if not lp then return end
    local lp_alive = safe(lp.alive, lp) == true
    local lp_eye = safe(lp.eye_position, lp)
    if not lp_eye then return end

    local now, tick, rt = globals.curtime(), globals.tickcount(), STATE.rt
    local va = safe(engine.view_angles)
    local players = safe(entity.players)
    if type(players) ~= "table" then return end
    local cross, cross_fov = nil, C.FOCUS_FOV
    for i = 1, #players do
        local p = players[i]
        local pawn = p.pawn
        if pawn and safe(pawn.alive, pawn) == true and safe(pawn.is_enemy, pawn) == true then
            local addr = safe(pawn.address, pawn)
            if addr then
                local ok, rec = pcall(RES.process, pawn, p.controller, addr, lp, lp_alive, lp_eye, now, tick, rt)
                if not ok then
                    report("process", rec)
                elseif rec and va and rec.en_eye then
                    local fov = U.fov(lp_eye, rec.en_eye, va)
                    if fov < cross_fov then cross, cross_fov = rec, fov end
                end
            end
        end
    end
    -- The ragebot's own target has priority; the crosshair record is only the fallback.
    local focus = cross
    local trec = RB.t_addr and RES.by_pawn[RB.t_addr] or nil
    if trec and trec.resolved and rt - trec.seen_rt < 0.5 then focus = trec end
    RES.focus = focus
    RES.check_flip()

    RES.check_pending(now)
    RES.purge(rt)
end

-- ---------------------------------------------------------------- lifecycle
function RES.reset_volatile()
    RES.pending = {}
    for _, rec in pairs(RES.records) do
        RES.reset_history(rec)
        rec.conf = rec.conf * C.ROUND_CONF_DECAY
    end
end

function ACT.reset_learn()
    RES.records, RES.by_pawn, RES.pending, RES.store = {}, {}, {}, {}
    for k in pairs(RES.stats) do RES.stats[k] = 0 end
    RES.reset_signs()
    RES.focus, RES.store_dirty = nil, false
    safe(db.save, META.db, {})
    notify("Learned data cleared")
end

function RES.on_round_start()
    RES.reset_volatile()
    RES.store_save(false)
end

function RES.on_level_init()
    RES.records, RES.by_pawn, RES.pending = {}, {}, {}
    RES.focus = nil
    RES.body_good, RES.body_bad, RES.body_ok = 0, 0, true
    RES.node_good, RES.node_bad, RES.node_ok, RES.node_field = 0, 0, true, nil
    RES.simtime_ok = true
    RES.write_fails = 0
    RES.ack.n, RES.ack.t = 0, -1e9
    if RES.write_ok == false then RES.write_ok, RES.write_cls = nil, nil end
end

function RES.on_level_shutdown()
    RES.store_save(false)
    RES.records, RES.by_pawn, RES.pending = {}, {}, {}
    RES.focus = nil
end

-- ============================================================================
--  RESOLVER · 4.2 additions
--    · two-cluster jitter model (1-D 2-means on the circle, tightness-weighted confidence)
--    · side memory per AA class
--    · blacklist of effective offsets that just missed
--    · continuous trust score (drives the headshot assist)
-- ============================================================================
-- Fields added in 4.2 (kept out of new_record so the v4.1 record layout stays readable).
function RES.extend(rec)
    rec.tried, rec.cls, rec.good_idx, rec.jit_tight = {}, {}, nil, 0
    return rec
end

-- Two-angle jitter model. The split point is refined like 1-D 2-means: clusters are the samples
-- on either side of the current center, the center moves to the midpoint of both cluster means.
-- Tightness (how close the samples sit to +-half) scales the prediction confidence, so 3-way /
-- random patterns that only look like jitter fall back to the center handling.
function RES.jitter_model(rec)
    local H, n, yaws, c0 = C.HISTORY, rec.n, rec.yaws, rec.center
    local hi, lo = 0, 0
    for _ = 1, 3 do
        local hs, hn, ls, ln = 0, 0, 0, 0
        for i = 1, n do
            local o = normalize(yaws[i] - c0)
            if o >= 0 then hs, hn = hs + o, hn + 1 else ls, ln = ls + o, ln + 1 end
        end
        if hn == 0 or ln == 0 then
            rec.jit_pconf = 0
            return
        end
        hi, lo = hs / hn, ls / ln
        local shift = (hi + lo) * 0.5
        c0, hi, lo = normalize(c0 + shift), hi - shift, lo - shift
        if abs(shift) < 0.5 then break end
    end
    local half = (hi - lo) * 0.5
    local dev = 0
    for i = 1, n do dev = dev + abs(abs(normalize(yaws[i] - c0)) - half) end
    local tight = clamp(1 - (dev / n) / max(4, half * 0.5), 0, 1)
    rec.center, rec.jit_half, rec.amp, rec.jit_tight = c0, half, half, tight

    local idx = (n == H) and (rec.head % H + 1) or 1        -- oldest sample first
    local side, run, runs, rn = 0, 0, RES.runs, 0
    for _ = 1, n do
        local sd = (normalize(yaws[idx] - c0) >= 0) and 1 or -1
        if sd == side then
            run = run + 1
        else
            if side ~= 0 then rn = rn + 1 runs[rn] = run end
            side, run = sd, 1
        end
        idx = idx % H + 1
    end
    local first = (rn >= 3) and 2 or 1                       -- the oldest run is cut by the window
    local total = rn - first + 1
    local best, best_n = 1, 0
    for p = 1, C.JIT_MAX_PERIOD do
        local cnt = 0
        for i = first, rn do
            if runs[i] == p then cnt = cnt + 1 end
        end
        if cnt > best_n then best, best_n = p, cnt end
    end
    rec.jit_period, rec.jit_side, rec.jit_run = best, side, run
    rec.jit_pconf = (total >= 2) and (best_n / total) * (0.5 + 0.5 * tight) or 0
end

-- Effective signed offset of a brute entry, as a table key (side x multiplier, 1/100 steps).
function RES.eff_key(side, mult) return floor(side * mult * 100 + 0.5) end

-- Next brute index after a resolver miss. Entries whose effective offset missed within
-- TRIED_TTL are skipped; when all of them failed the memory is cleared and the list restarts
-- at the entry that hit last (or simply at the next one).
function RES.next_brute(rec, shot)
    local len, now, tried = RES.brute_len(), STATE.rt, rec.tried
    tried[RES.eff_key(shot.side, (RES.brute_entry(rec, shot.idx)))] = now
    local idx = rec.brute_idx
    if not CFG.brute_skip then return idx % len + 1 end
    for _ = 1, len do
        idx = idx % len + 1
        local t = tried[RES.eff_key(rec.pred_side, (RES.brute_entry(rec, idx)))]
        if not t or now - t >= C.TRIED_TTL or now < t then return idx end
    end
    for k in pairs(tried) do tried[k] = nil end
    local good = rec.good_idx
    if good and good ~= rec.brute_idx and good <= len then return good end
    return rec.brute_idx % len + 1
end

-- Confirmed (non partial) hit: the class that was live at fire time learns the side.
function RES.note_hit(rec, shot, confirmed)
    if not confirmed then return end
    rec.good_idx = shot and shot.idx or rec.brute_idx
    local mode = shot and shot.mode or rec.mode
    local c = rec.cls[mode]
    if not c then
        c = { side = rec.side, w = 0 }
        rec.cls[mode] = c
    end
    if c.side ~= rec.side then c.side, c.w = rec.side, 0 end
    c.w = min(1, c.w + C.CLS_GAIN)
    for k in pairs(rec.tried) do rec.tried[k] = nil end
end

-- Resolver miss with a full-desync entry: the class memory for that side weakens.
function RES.note_miss(rec, shot, wrong_side, w)
    local c = rec.cls[shot.mode or rec.mode]
    if c and c.side == wrong_side then c.w = max(0, c.w - C.CLS_LOSS * (w or 1)) end
end

function RES.class_bias(rec)
    if not CFG.cls_mem then return 0 end
    local c = rec.cls[rec.mode]
    if not c then return 0 end
    return c.side * c.w * C.W_CLASS
end

-- How much the current guess can be trusted, 0..1. One number for the panel, the debug view
-- and the headshot assist; RES.unresolved stays the hard "do not trust" gate.
function RES.trust(rec)
    if not rec or not rec.resolved or rec.lc then return 0 end
    local t = 0.25 + rec.conf * 0.45
    local mode = rec.mode
    if mode == "static" then t = t + 0.20 * rec.mode_conf
    elseif mode == "sway" then t = t + 0.08
    elseif mode == "jitter" then t = t + ((rec.jit_k ~= nil) and 0.18 * rec.jit_pconf or -0.10)
    elseif mode == "spin" then t = t - 0.10
    else t = t - 0.20 end
    local c = rec.cls[mode]
    if c and c.side == rec.pred_side then t = t + 0.10 * c.w end
    t = t + min(0.15, rec.hit_streak * 0.05) - min(0.30, rec.miss_streak * 0.15) - min(0.20, (rec.brute_idx - 1) * 0.05)
    if rec.moving then t = t - 0.05 end
    if rec.manual then t = max(t, 0.6) end
    return clamp(t, 0, 1)
end

-- ============================================================================
--  CHANNEL 1 · createmove correction
--  The ragebot aims at the model it sees (raw networked yaw). The resolved body yaw differs
--  by delta = resolved - raw. When a command fires, the aim point is rotated around the
--  target's vertical axis by delta and the command is re-aimed there. The full delta is
--  applied: a clamped correction would aim between the fake and the real model.
--  Movement is rotated with the documented cmd:rotate_movement() so the correction never
--  changes where we walk. Skipped when the angles are already written into memory (channel 2)
--  or the target breaks lag compensation.
-- ============================================================================
-- CS2 may put the attack press into a subtick while the command's own button mask is clear.
local function attack_active(cmd)
    if cmd:has(K.BTN_ATTACK) then return true end
    local ok, subs = pcall(cmd.subticks, cmd)
    if not ok or type(subs) ~= "table" then return false end
    for i = 1, #subs do
        local s = subs[i]
        if type(s) == "table" and s.button == K.BTN_ATTACK
            and s.pressed ~= false and s.is_button ~= false then return true end
    end
    return false
end

-- Subtick shots carry their own view angles; rotate them together with the command.
local function offset_subticks(cmd, dyaw, dpit)
    local ok, subs = pcall(cmd.subticks, cmd)
    if not ok or type(subs) ~= "table" then return end
    for i = 1, #subs do
        local s = subs[i]
        if type(s) == "table" then
            if type(s.yaw) == "number" then s.yaw = normalize(s.yaw + dyaw) end
            if type(s.pitch) == "number" then s.pitch = clamp(s.pitch + dpit, -89, 89) end
        end
    end
end

-- Record the firing command aims at: the ragebot target first, else the closest tracked enemy.
function RES.aim_record(eye, va)
    local best, best_fov = nil, C.CMD_FOV
    local rt = STATE.rt
    local trec = RB.t_addr and RES.by_pawn[RB.t_addr] or nil
    for _, rec in pairs(RES.records) do
        local o = rec.last_origin
        if o and rec.resolved and rt - rec.seen_rt < 0.2 then
            local fov = U.fov(eye, vector(o.x, o.y, o.z + K.EYE_OFFSET * 0.6), va)
            if rec == trec then fov = fov * 0.5 end      -- priority for the ragebot target
            if fov < best_fov then best, best_fov = rec, fov end
        end
    end
    return best
end

function RES.cmd_fix(cmd, lp)
    if not CFG.enable or not CFG.cmd_fix then return end
    if not attack_active(cmd) then return end
    local va = safe(cmd.view_angles, cmd)
    local eye = safe(lp.eye_position, lp)
    if not va or not eye then return end
    local rec = RES.aim_record(eye, va)
    if not rec or rec.mem_written or rec.lc then return end
    local delta = normalize(rec.resolved_yaw - rec.raw_yaw)
    if abs(delta) < C.CMD_MIN then return end
    -- current (interpolated) origin: last_origin is only the position from the last net update
    local o = (rec.pawn and safe(rec.pawn.origin, rec.pawn)) or rec.last_origin
    if not o then return end

    -- point of the aim ray closest to the target's vertical axis
    local pitch, yaw = va.x, va.y
    local cp = cos(rad(pitch))
    local fx, fy, fz = cp * cos(rad(yaw)), cp * sin(rad(yaw)), -sin(rad(pitch))
    local l2 = fx * fx + fy * fy
    if l2 < 1e-4 then return end
    local t = ((o.x - eye.x) * fx + (o.y - eye.y) * fy) / l2
    if t <= 0 then return end
    local px, py, pz = eye.x + fx * t, eye.y + fy * t, eye.z + fz * t

    -- rotate it around the axis by delta and aim there
    local a = rad(delta)
    local ca, sa = cos(a), sin(a)
    local rx, ry = px - o.x, py - o.y
    local dx, dy, dz = o.x + rx * ca - ry * sa - eye.x, o.y + rx * sa + ry * ca - eye.y, pz - eye.z
    local dyaw = normalize(deg(atan2(dy, dx)) - yaw)
    local dpit = deg(atan2(-dz, sqrt(dx * dx + dy * dy))) - pitch
    if abs(dyaw) < 0.01 and abs(dpit) < 0.01 then return end
    -- CMD_MAX is a sanity bound, not a partial-correction clamp: an implausible result is
    -- dropped instead of turning the shot into a guaranteed miss between the two models.
    if abs(dyaw) > C.CMD_MAX or abs(dpit) > C.CMD_MAX then return end

    local ang = vector(clamp(pitch + dpit, -89, 89), normalize(yaw + dyaw), 0)
    if not pcall(cmd.set_view_angles, cmd, ang) then return end
    pcall(cmd.lock_angles, cmd)                       -- keep the client from overwriting the fix
    if CFG.rotate_move then pcall(cmd.rotate_movement, cmd, dyaw) end
    offset_subticks(cmd, dyaw, dpit)
end

RES.reset_signs()
return RES
end
