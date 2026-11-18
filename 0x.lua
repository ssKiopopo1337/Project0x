-- @author 0x
-- @uid 0

-- ============================================================================
--  0x  ·  v4.5 Power Plus  ·  resolver + rage assist
--  Neverlose CS2 Lua  ·  API: github.com/PbLJk/neverlose-lua-api (lowercase API)
--
--  Credits: @kukluxk · @likvidatorchaes (subcult)
--
--  FILES
--    0x.lua           menu, rage assist, visuals, lifecycle   (this file)
--    0x_resolver.lua  resolver (loaded with require; the rest keeps running if it fails)
--
--  FILE MAP
--    MENU        registry, :callback() driven settings, layout (BUILD.*), snapshot, IO
--    RAGE ASSIST journal, config binding, movement state, targets, headshot assist, decision
--    VISUALS     overlay, yaw lines, status panel, event feed
--    LIFECYCLE   per-module fail-safes, hooks, boot
--
--  NEW IN 4.5
--    · two delivery channels for the resolved yaw: createmove (cmd view angles corrected on
--      fire, movement rotated) and, optionally, m_angEyeAngles in memory (Allow Insecure)
--    · misses are classified hard (death / lost / lagcomp / local: no learning) or soft
--      (moving / airborne / spread / off_target: learning with half weight)
--    · events.aim_ack (ragebot.Shot.result) is the primary miss source, heuristics fall back
--    · body hint reads the scene node rotation (no hitbox tables); hitboxes are the fallback
--    · hint reliability: a one-time sign flip when a hint's weight reaches the floor
--    · menu is driven by :callback() instead of polling; combo base is detected per widget
--    · every module (core / resolver / rage / visuals) has its own error budget
--    · headshot assist is off by default, config write logging is on by default
--    · hitchance bonuses respect an overall cap; damage gate needs a measured body damage
-- ============================================================================

local META = {
    name        = "0x",
    version     = "4.5",
    edition     = "Power Plus",
    schema      = 6,
    module      = "0x_resolver",         -- require() name of the resolver file
    db          = "0x_resolver_v21",     -- learned sides (compatible with v2.1+)
    db_settings = "0x_v45_settings",     -- menu snapshot
    db_prev     = "0x_v4_settings",      -- 4.x snapshot, imported once
    db_journal  = "0x_v31_journal",      -- ragebot originals (crash-safe)
    db_import   = "0x_import",           -- data\db\0x_import.json
    db_export   = "0x_export",           -- data\db\0x_export.json
    credits     = "@kukluxk · @likvidatorchaes (subcult)",
    import_max  = 65536,                 -- bytes; larger pasted snapshots are rejected
}

-- Manual config paths when auto-discovery picks the wrong ones. Example: hc = { "ragebot.hitchance" }
-- Paths imported from a snapshot (web companion) are merged with these.
local CUSTOM_PATHS = { hc = {}, dmg = {}, safe = {}, baim = {}, hitbox = {} }
-- If safepoint in your ragebot is a dropdown, this is the index of the "Force" item.
local SAFE_COMBO_VALUE = 2

-- ----------------------------------------------------------------------------
-- Fast paths and helpers
-- ----------------------------------------------------------------------------
local floor, abs, sqrt, atan2, sin, cos, rad, deg = math.floor, math.abs, math.sqrt, math.atan2, math.sin, math.cos, math.rad, math.deg
local max, min = math.max, math.min
local pcall, pairs, type, tostring, tonumber, next = pcall, pairs, type, tostring, tonumber, next
local format, s_lower, s_find, s_gsub, s_sub = string.format, string.lower, string.find, string.gsub, string.sub
local tremove, tconcat, tsort = table.remove, table.concat, table.sort
local band = bit.band
local function normalize(a)
    a = a % 360
    if a > 180 then a = a - 360 end
    return a
end
local function clamp(v, lo, hi) if v < lo then return lo elseif v > hi then return hi end return v end
local function lerp(a, b, t) return a + (b - a) * t end
local function round(v) return floor(v + 0.5) end
local function sign(v) if v > 0 then return 1 elseif v < 0 then return -1 end return 0 end

-- Calls fn and swallows errors. Returns only the first result.
local function safe(fn, ...)
    if fn == nil then return nil end
    local ok, r = pcall(fn, ...)
    if ok then return r end
    return nil
end

-- Utility namespace (kept in one table to stay far below LuaJIT's 200-locals limit).
local U = {}

function U.copy(v)
    if type(v) ~= "table" then return v end
    local o = {}
    for k, x in pairs(v) do o[k] = x end
    return o
end

local function same_scalar(a, b)
    if a == b then return true end
    if type(a) == "number" and type(b) == "number" then return abs(a - b) < 1e-4 end
    return false
end

-- Shallow structural equality (config values: numbers, booleans, strings, flat tables).
function U.same(a, b)
    if same_scalar(a, b) then return true end
    if type(a) ~= "table" or type(b) ~= "table" then return false end
    for k, v in pairs(a) do
        if not same_scalar(v, b[k]) then return false end
    end
    for k in pairs(b) do
        if a[k] == nil then return false end
    end
    return true
end

function U.any_match(s, list)
    for i = 1, #list do
        if s_find(s, list[i]) then return true end
    end
    return false
end

function U.utf8_len(s) return select(2, s_gsub(s, "[^\128-\193]", "")) end

function U.trim(s) return (s_gsub(s, "^%s+", ""):gsub("%s+$", "")) end

-- Angular distance of a direction (from -> to) to view angles va.
function U.fov(from, to, va)
    local dx, dy, dz = to.x - from.x, to.y - from.y, to.z - from.z
    local pitch = deg(atan2(-dz, sqrt(dx * dx + dy * dy)))
    local yaw = deg(atan2(dy, dx))
    local dp, dw = normalize(pitch - va.x), normalize(yaw - va.y)
    return sqrt(dp * dp + dw * dw)
end

-- Yaw of the direction from -> to (degrees).
function U.yaw_to(from, to) return deg(atan2(to.y - from.y, to.x - from.x)) end


local function get_weapon_info(pawn)
    if not pawn then return nil end
    local info = safe(pawn.weapon_info, pawn)
    if type(info) == "table" then return info end
    local w = safe(pawn.weapon, pawn)
    if w then
        info = safe(w.weapon_info, w)
        if type(info) == "table" then return info end
    end
    return nil
end

local function say(msg) print("[0x] " .. tostring(msg)) end
-- ----------------------------------------------------------------------------
-- Constants
-- ----------------------------------------------------------------------------
local K = {
    EVAL_TICKS   = 4,          -- target / lethality re-evaluation period, ticks
    VERIFY_TICKS = 16,         -- config cross-check period, ticks
    WEAPON_TICKS = 64,         -- weapon class re-check period, ticks
    HK_INTERVAL  = 1.0,        -- housekeeping period, s
    SAVE_DELAY   = 1.5,        -- autosave delay after the last menu change, s
    JOURNAL_LAZY = 15,         -- s of silence before stale journal entries are dropped from disk
    IO_RETRY     = 5,          -- pause after a failed disk write, s
    CM_TIMEOUT   = 0.5,        -- createmove silent longer than this -> ragebot values restored, s
    PAINT_TIMEOUT = 2,         -- paint silent longer than this -> createmove runs background tasks, s
    MAX_CANDS    = 48,         -- path candidates per parameter
    MAX_TARGETS  = 3,          -- closest-to-crosshair targets to trace
    HOLD_TICKS   = 12,         -- body-aim decision hold (anti flicker)
    MOVE_EPS     = 5,          -- "moving" threshold, u/s
    T_MOVE_SQR   = 1600,       -- target "running" above 40 u/s (squared)
    T_WALK_SQR   = 19600,      -- target "running" above 140 u/s (squared)
    BAD_LIMIT    = 3,          -- consecutive write failures before a path is disabled
    MISM_LIMIT   = 3,          -- consecutive foreign overwrites before a path is disabled
    ERR_LIMIT    = 25,         -- consecutive callback errors before a module is suspended
    ERR_COOLDOWN = 5,          -- suspension length, s
    ERR_STRIKES  = 3,          -- suspensions before a module stops
    ERR_FORGIVE  = 60,         -- s without errors after which strikes are forgotten
    EYE_OFFSET   = 46,         -- aim point height above the target origin
    HB_TTL       = 256,        -- hitbox id cache lifetime, ticks
    HB_MAX       = 64,
    GRAVITY      = 800,
    SIM_MARGIN   = 16,
    MEMO_MAX     = 512,
    FEED_LIFE    = 5.0,        -- s; event feed line lifetime
    FEED_MAX     = 6,
    HG_HEAD = 1, HG_CHEST = 2, HG_STOMACH = 3,
    FL_DUCKING   = 2,
    BTN_ATTACK   = (buttons and buttons.attack) or 1,
    BTN_LEFT     = (buttons and buttons.left) or 512,      -- IN_MOVELEFT
    BTN_RIGHT    = (buttons and buttons.right) or 1024,    -- IN_MOVERIGHT
    BTN_SPEED    = (buttons and buttons.speed) or 65536,
    VK_LBUTTON   = 1,
}

local E = {
    MODE_ADAPTIVE = 1, MODE_STATIC = 2, MODE_BRUTE = 3, MODE_JITSPIN = 4, MODE_OFFSET = 5,
    JIT_CENTER = 1, JIT_PREDICT = 2, JIT_FOLLOW = 3,
    BASE_AUTO = 1, BASE_EYE = 2, BASE_TARGET = 3,
    PITCH_OFF = 1, PITCH_CLAMP = 2, PITCH_AUTO = 3, PITCH_DOWN = 4, PITCH_ZERO = 5, PITCH_UP = 6,
    PAT_MULT = 1, PAT_STEP = 2,
    STAGE_LAGCOMP = (stage and stage.lagcomp) or 6,
    STAGE_NET_END = (stage and stage.net_update_end) or 7,
    MASK_VISIBLE  = (trace and trace.mask and trace.mask.visible) or 1847299,
}
local MODE_LABEL  = { static = "STATIC", sway = "SWAY", jitter = "JITTER", spin = "SPIN", random = "RANDOM" }

local ST = { STAND = 1, SLOW = 2, MOVE = 3, DUCK = 4, AIR = 5, APEX = 6 }
local ST_NAME = { "STAND", "WALK", "RUN", "DUCK", "AIR", "APEX" }

local WPN = {
    ITEMS = { "SSG 08", "AWP", "Auto snipers", "Deagle / R8", "Pistols", "Other" },
    BY_DEF = {
        [40] = 1, [9] = 2, [11] = 3, [38] = 3, [1] = 4, [64] = 4,
        [2] = 5, [3] = 5, [4] = 5, [30] = 5, [32] = 5, [36] = 5, [61] = 5, [63] = 5,
    },
    BY_NAME = {
        { "ssg08", 1 }, { "awp", 2 }, { "g3sg1", 3 }, { "scar20", 3 }, { "deagle", 4 }, { "revolver", 4 },
        { "elite", 5 }, { "fiveseven", 5 }, { "glock", 5 }, { "tec9", 5 }, { "hkp2000", 5 },
        { "p250", 5 }, { "usp", 5 }, { "cz75", 5 },
    },
    NON_GUN = {
        "knife", "bayonet", "grenade", "flashbang", "smoke", "molotov", "incgrenade", "decoy", "c4",
        "taser", "healthshot", "fists", "melee", "axe", "hammer", "spanner", "tablet", "shield",
        "breach", "bump", "inferno",
    },
    NON_GUN_DEF = { [31] = true, [41] = true, [42] = true, [57] = true, [59] = true, [69] = true,
                    [70] = true, [72] = true, [74] = true, [75] = true, [76] = true, [78] = true, [85] = true },
}
for d = 43, 49 do WPN.NON_GUN_DEF[d] = true end
for d = 500, 526 do WPN.NON_GUN_DEF[d] = true end

function WPN.non_gun_name(name)
    if type(name) ~= "string" or name == "" then return false end
    local l = s_lower(name)
    for i = 1, #WPN.NON_GUN do
        if s_find(l, WPN.NON_GUN[i], 1, true) then return true end
    end
    return false
end

-- ----------------------------------------------------------------------------
-- Shared runtime state
-- ----------------------------------------------------------------------------
local STATE = {
    rt = 0,                                -- realtime snapshot for the current callback
    insecure = false,
    menu_open = false, menu_evt_t = -1e9, menu_poll_t = -1e9,
    raw_p = nil, raw_y = nil,              -- cmd angles as the ragebot set them
    cmd_p = nil, cmd_y = nil,              -- cmd angles actually sent (after the resolver correction)
    lp_air = false, lp_moving = false, lp_dead = true,
    sw = 0, sh = 0,
    rep_last = nil, rep_t = -100,
    last_label = 0,
    flip_prev = false,
}

-- Module health: each module has its own error budget and is suspended on its own.
local MODS = {}
for _, name in pairs({ "core", "res", "rage", "vis" }) do
    MODS[name] = { errs = {}, strikes = 0, strike_t = 0, hold = nil, dead = false }
end

-- Tables instead of locals keep every closure far below LuaJIT's 60-upvalue limit.
local RB, VIS, ACT, Bind, Journal, IO = {}, {}, {}, {}, {}, {}

local function report(where, err)
    local msg = tostring(err)
    if msg ~= STATE.rep_last or STATE.rt - STATE.rep_t > 5 then
        STATE.rep_last, STATE.rep_t = msg, STATE.rt
        say("error in " .. where .. ": " .. msg)
    end
end

-- ============================================================================
--  MENU: registry, :callback() driven settings, snapshot
-- ============================================================================
local UI, REG, ORDER, CFG = {}, {}, {}, {}
local MENU = { built = false, poll_t = -1e9 }
local SET = { dirty = false, dirty_t = 0, io_t = -1e9 }
local PS = { last = nil, sync = true, applying = false }
local PATHS_USER = { hc = {}, dmg = {}, safe = {}, baim = {}, hitbox = {} }   -- from snapshots
local POLL = {}                    -- widgets whose :callback() could not be installed (polled at 1 Hz)

-- A failed element must not take the script down: it is replaced by an inert stand-in.
local DUMMY = setmetatable({}, { __mode = "k" })
local function is_dummy(el) return el == nil or DUMMY[el] == true end

local function dummy_el(def)
    local d = {}
    DUMMY[d] = true
    d.get = function() return def end
    d.set = function() end
    d.depends = function() return d end
    d.tooltip = function() return d end
    d.callback = function() return d end
    d.visible = function() return false end
    d.active = function() return false end
    return d
end

local function create(g, ctor, id, def, ...)
    if type(ctor) ~= "function" then return dummy_el(def) end
    local ok, el = pcall(ctor, g, ...)
    if not ok or el == nil then
        say("menu element '" .. tostring(id) .. "' not created: " .. tostring(el))
        el = dummy_el(def)
    end
    return el
end

-- multi_combo value may arrive as {[name]=bool}, {bool,...} or a list of selected names / indices.
local function multi_on(v, idx, items)
    if type(v) ~= "table" then return false end
    local name = items[idx]
    local x = v[name]
    if x ~= nil then return x == true end
    x = v[idx]
    if type(x) == "boolean" then return x end
    for i = 1, #v do
        local e = v[i]
        if e == name or e == idx or e == idx - 1 then return true end
    end
    return false
end

local function bind_on(el)
    if el == nil or is_dummy(el) then return false end
    local ok, v = pcall(el.active, el)
    return ok and v == true
end

local function notify(msg)
    if CFG.notif ~= false then pcall(client.notify, msg, META.name) end
    say(msg)
end

local on_widget

-- Combos are 1-based everywhere in this script. The widget base is detected PER WIDGET from
-- the value of its first item: a string means "by name", a number is the base (0 or 1).
local function probe_combo(r)
    local v = safe(r.el.get, r.el)
    if type(v) == "string" then
        r.named = true
    elseif type(v) == "number" then
        r.base = (v == 0) and 0 or 1
    end
end

local function set_combo(r, idx1)
    local el = r.el
    if is_dummy(el) then return end
    if r.named then
        pcall(el.set, el, r.items[idx1])
    else
        pcall(el.set, el, (r.base or 1) + idx1 - 1)
    end
end

local function combo_index(r)
    local v = safe(r.el.get, r.el)
    local items = r.items
    if type(v) == "number" then
        return clamp(floor(v + 0.5) - (r.base or 1) + 1, 1, #items)
    elseif type(v) == "string" then
        for i = 1, #items do
            if items[i] == v then return i end
        end
    end
    return nil
end

local function reg(id, kind, el, def, lo, hi, items, tip)
    local r = { id = id, kind = kind, el = el, def = def, lo = lo, hi = hi, items = items }
    REG[id], UI[id] = r, el
    ORDER[#ORDER + 1] = id
    CFG[id] = def
    if not is_dummy(el) then
        if tip then pcall(el.tooltip, el, tip) end
        if kind == "combo" then probe_combo(r) end
        if kind ~= "key" then
            local cb = el.callback
            local fn = function()
                local ok, err = pcall(on_widget, r)
                if not ok then report("menu", err) end
            end
            if not (type(cb) == "function" and pcall(cb, el, fn)) then POLL[#POLL + 1] = r end
        end
    end
    return el
end

local W = {}   -- widget constructors

function W.chk(g, id, name, def, tip)
    return reg(id, "check", create(g, g.checkbox, id, def, name, def), def, nil, nil, nil, tip)
end

function W.sld(g, id, name, lo, hi, def, fmt, tip)
    return reg(id, "slider", create(g, g.slider_int, id, def, name, lo, hi, def, fmt or "%d"), def, lo, hi, nil, tip)
end

function W.cmb(g, id, name, items, def1, tip)
    local el = reg(id, "combo", create(g, g.combo, id, def1, name, items, def1), def1, 1, #items, items, tip)
    if def1 > 1 then set_combo(REG[id], def1) end
    return el
end

function W.clr(g, id, name, def, tip)
    return reg(id, "color", create(g, g.color, id, def, name, def, true), def, nil, nil, nil, tip)
end

function W.key(g, id, name, tip)
    return reg(id, "key", create(g, g.keybind, id, false, name, 0), false, nil, nil, nil, tip)
end

function W.mcb(g, id, name, items, defs, tip)
    return reg(id, "multi", create(g, g.multi_combo, id, defs, name, items, defs), defs, nil, nil, items, tip)
end

function W.lbl(g, text)
    return create(g, g.label, "label", nil, text)
end

function W.btn(g, id, name, act, tip)
    local el = create(g, g.button, id, nil, name, function()
        local f = ACT[act]
        if not f then return end
        STATE.rt = globals.realtime()
        local ok, err = pcall(f)
        if not ok then report("button " .. act, err) end
    end)
    if tip and not is_dummy(el) then pcall(el.tooltip, el, tip) end
    return el
end

function W.div(g, text) if type(g.divider) == "function" then pcall(g.divider, g, text) end end

function W.dep(el, other)
    if is_dummy(el) or is_dummy(other) then return el end
    pcall(el.depends, el, other)
    return el
end

local ITEMS = {
    MODE    = { "Adaptive", "Static side", "Bruteforce", "Jitter / Spin", "Static offset" },
    JIT     = { "Center", "Predict next", "Follow last" },
    BASE    = { "Auto", "Eye yaw", "At target" },
    PITCH   = { "Off", "Clamp", "Auto", "Force down", "Force zero", "Force up" },
    BRUTE   = { "Multipliers", "Stepped" },
    OVERLAY = { "Compact", "Detailed" },
    PRESET  = { "Custom", "Balanced", "Aggressive", "Conservative" },
    AIR     = { "Ground + vertical speed", "Ground flag only", "Landing prediction" },
    HS_NEED   = { "Head shot is lethal", "Head beats body", "Whenever trusted" },
    HS_STATES = { "Standing", "Ducking", "Walking", "Running" },
}

local PRESETS = {
    [2] = { name = "Balanced", air_hc = 70, apex_hc = 58, air_dmg = 50, hc_stand = 70, hc_slow = 65, hc_move = 55,
            hc_duck = 72, hc_tgt_air = -8, hc_tgt_move = 0, strict_bonus = 12, baim_margin = 2,
            baim_lethal = true, baim_2x = false, dmg_cap = true },
    [3] = { name = "Aggressive", air_hc = 58, apex_hc = 48, air_dmg = 38, hc_stand = 60, hc_slow = 55, hc_move = 45,
            hc_duck = 62, hc_tgt_air = -12, hc_tgt_move = -4, strict_bonus = 8, baim_margin = 0,
            baim_lethal = true, baim_2x = true, dmg_cap = true },
    [4] = { name = "Conservative", air_hc = 78, apex_hc = 68, air_dmg = 62, hc_stand = 80, hc_slow = 75, hc_move = 66,
            hc_duck = 82, hc_tgt_air = -4, hc_tgt_move = 0, strict_bonus = 16, baim_margin = 5,
            baim_lethal = true, baim_2x = false, dmg_cap = true },
}

-- A tab or group that fails to build becomes an empty table: every constructor then falls
-- through create() into an inert stand-in and the script keeps running with defaults.
local function mk_tab(name)
    local ok, t = pcall(ui.tab, name)
    if not ok or not t then
        say("tab '" .. name .. "' not created: " .. tostring(t))
        return {}
    end
    return t
end

local function mk_group(tab, name)
    if type(tab.group) ~= "function" then return {} end
    local ok, g = pcall(tab.group, tab, name)
    if not ok or not g then
        say("group '" .. name .. "' not created: " .. tostring(g))
        return {}
    end
    return g
end

-- ---------------------------------------------------------------- values
local function read(r)
    local el = r.el
    local ok, v = pcall(el.get, el)
    if not ok or v == nil then return CFG[r.id] end
    local k = r.kind
    if k == "check" then return v == true end
    if k == "slider" then
        v = tonumber(v)
        if not v then return r.def end
        return clamp(floor(v + 0.5), r.lo, r.hi)
    end
    if k == "combo" then return combo_index(r) or r.def end
    if k == "color" then
        if type(v) == "table" and type(v.r) == "number" and type(v.g) == "number" and type(v.b) == "number" then
            return { r = clamp(v.r, 0, 255), g = clamp(v.g, 0, 255), b = clamp(v.b, 0, 255), a = clamp(tonumber(v.a) or 255, 0, 255) }
        end
        return r.def
    end
    if k == "multi" and type(v) == "table" then return U.copy(v) end
    return v
end

local function differs(kind, a, b)
    if kind == "color" and type(a) == "table" and type(b) == "table" then
        return a.r ~= b.r or a.g ~= b.g or a.b ~= b.b or a.a ~= b.a
    end
    if kind == "multi" then return not U.same(a, b) end
    return a ~= b
end

-- Converts a stored / imported value into a valid value for the element (nil = reject).
local function validate(r, v)
    local k = r.kind
    if k == "check" then
        if type(v) == "boolean" then return v end
    elseif k == "slider" then
        v = tonumber(v)
        if v then return clamp(floor(v + 0.5), r.lo, r.hi) end
    elseif k == "combo" then
        if type(v) == "string" then
            for i = 1, #r.items do
                if r.items[i] == v then return i end
            end
            return nil
        end
        v = tonumber(v)
        if v then return clamp(floor(v + 0.5), 1, #r.items) end
    elseif k == "color" then
        if type(v) == "table" and type(v.r) == "number" and type(v.g) == "number" and type(v.b) == "number" then
            return { r = clamp(v.r, 0, 255), g = clamp(v.g, 0, 255), b = clamp(v.b, 0, 255), a = clamp(tonumber(v.a) or 255, 0, 255) }
        end
    elseif k == "multi" then
        if type(v) == "table" then
            local m = {}
            for j = 1, #r.items do m[r.items[j]] = multi_on(v, j, r.items) end
            return m
        end
    end
    return nil
end

local function write_el(r, v)
    local el = r.el
    if is_dummy(el) then CFG[r.id] = v return end
    local k = r.kind
    if k == "combo" then
        set_combo(r, v)
    elseif k == "color" then
        pcall(el.set, el, color(v.r, v.g, v.b, v.a or 255))
    elseif k == "multi" then
        local cur = safe(el.get, el)
        local payload = v
        if type(cur) == "table" and #cur > 0 and type(cur[1]) == "boolean" then
            local arr = {}
            for j = 1, #r.items do arr[j] = multi_on(v, j, r.items) end
            payload = arr
        elseif type(cur) == "table" then
            local map = {}
            for j = 1, #r.items do map[r.items[j]] = multi_on(v, j, r.items) end
            payload = map
        end
        pcall(el.set, el, payload)
    else
        pcall(el.set, el, v)
    end
end

local function derive()
    CFG.miss_win_s = (CFG.miss_win or 350) / 1000
    CFG.move_sc_f  = (CFG.move_sc or 35) / 100
    CFG.jit_sc_f   = (CFG.jit_sc or 50) / 100
end

-- Re-reads every widget (boot, import, reset, preset). Normal edits arrive through :callback().
local function refresh_all()
    for i = 1, #ORDER do
        local r = REG[ORDER[i]]
        if r.kind ~= "key" then CFG[r.id] = read(r) end
    end
    derive()
end

local function preset_matches(idx)
    local p = PRESETS[idx]
    if not p then return true end
    for id, v in pairs(p) do
        if id ~= "name" and CFG[id] ~= v then return false end
    end
    return true
end

local function apply_preset(idx)
    local p = PRESETS[idx]
    if not p then return end
    PS.applying = true
    for id, v in pairs(p) do
        if id ~= "name" and REG[id] then write_el(REG[id], v) end
    end
    PS.applying = false
    refresh_all()
    PS.last = CFG.preset
    if CFG.notif then pcall(client.notify, "Preset \"" .. p.name .. "\" applied", META.name) end
end

-- id == nil: values came from load / reset / import: the preset is not re-applied on top.
local function on_settings_changed(id)
    SET.dirty, SET.dirty_t = true, STATE.rt
    RB.eval_at = 0
    VIS.dirty = true
    if PS.applying or not REG.preset then return end
    local p = CFG.preset
    if id == "preset" then
        if p ~= PS.last then
            PS.last = p
            if p > 1 then apply_preset(p) end
        end
        return
    end
    -- Values drifted away from the selected preset: show "Custom". If the widget refuses the
    -- programmatic change we stop arguing with the user.
    if p > 1 and PS.sync and not preset_matches(p) then
        PS.applying = true
        write_el(REG.preset, 1)
        PS.applying = false
        local back = read(REG.preset)
        CFG.preset, PS.last = back, back
        if back ~= 1 then PS.sync = false end
    end
end

on_widget = function(r)
    local v = read(r)
    if not differs(r.kind, CFG[r.id], v) then return end
    CFG[r.id] = v
    STATE.rt = globals.realtime()
    derive()
    on_settings_changed(r.id)
end

-- Widgets that refused :callback() are polled once per second.
function MENU.poll(now)
    if #POLL == 0 or now - MENU.poll_t < 1 then return end
    MENU.poll_t = now
    for i = 1, #POLL do pcall(on_widget, POLL[i]) end
end

-- ---------------------------------------------------------------- menu layout (v4.2)
-- Four tabs, one job each. Every tab starts with its master switch; everything below it
-- depends on that switch. Element ids are unchanged since v4.0, so old snapshots still load.
--   0x Resolver  General · Jitter & brute · Hints · Learning
--   0x Rage      Assist · Headshot assist · Body-aim · Accuracy · Air · Binds · Config link
--   0x Visuals   Players · Panel · Style
--   0x Config    Settings · Data · About
local BUILD = {}

function BUILD.resolver()
    local chk, sld, cmb, key, dep = W.chk, W.sld, W.cmb, W.key, W.dep
    local tab = mk_tab("0x Resolver")

    local g = mk_group(tab, "General")
    local enable = chk(g, "enable", "Enable resolver", true, "Master switch of the resolver. The rage assist has its own switch on the 0x Rage tab.")
    dep(chk(g, "cmd_fix", "Correct aim on fire (createmove)", true, "Default channel. When the ragebot fires at a tracked enemy, the aim point is rotated by the resolved body yaw\nand the command is re-aimed (bounded to 12°). Needs no Allow Insecure."), enable)
    dep(chk(g, "rotate_move", "Rotate movement", true, "Rotates forward / side movement together with the corrected view so the correction never changes where you walk."), enable)
    dep(chk(g, "mem_write", "Write eye angles to memory", false, "Optional second channel: writes the resolved angles into m_angEyeAngles every net update.\nRequires Allow Insecure. Off by default; the createmove channel does not need it."), enable)
    dep(cmb(g, "mode", "Mode", ITEMS.MODE, E.MODE_ADAPTIVE,
        "Adaptive: all hints + learning + brute cycling.\nStatic side: learned side only.\nBruteforce: cycle the pattern on misses.\nJitter / Spin: jitter -> center, spin -> extrapolated yaw.\nStatic offset: yaw relative to you (Yaw offset)."), enable)
    dep(sld(g, "desync", "Max desync", 0, 90, 58, "%d°", "Desync amount applied to the base yaw."), enable)
    dep(sld(g, "yaw_off", "Yaw offset", -180, 180, 0, "%d°", "Static offset mode: resolved yaw = (yaw towards you) + offset."), enable)
    dep(cmb(g, "base", "Yaw base", ITEMS.BASE, E.BASE_AUTO, "Auto: spin -> at target, jitter -> center, otherwise eye yaw."), enable)
    dep(cmb(g, "pitch", "Pitch", ITEMS.PITCH, E.PITCH_AUTO, "Auto resolves fake pitch flicker to down and clamps the rest."), enable)
    dep(sld(g, "move_sc", "Moving correction", 0, 100, 35, "%d%%", "Share of the desync applied while the enemy moves."), enable)
    dep(chk(g, "face_damp", "Facing-target damping", true, "An eye yaw within 35° of you usually means he is aiming, not anti-aiming: desync is scaled down."), enable)
    key(g, "k_flip", "Flip target side", "Press: inverts the learned side of the crosshair target.")

    local gj = mk_group(tab, "Jitter & brute")
    dep(cmb(gj, "jit_mode", "Jitter handling", ITEMS.JIT, E.JIT_CENTER,
        "Center: aim at the middle of both jitter angles; a resolver miss steps to the predicted angle, then to the other one.\nPredict next: start at the angle the NEXT update is expected to have (both clusters and the switch period are learned; irregular patterns fall back to Center).\nFollow last: use the last received yaw."), enable)
    dep(sld(gj, "jit_sc", "Jitter correction", 0, 100, 50, "%d%%", "Share of the desync applied on top of the jitter center."), enable)
    dep(cmb(gj, "brute_pat", "Brute pattern", ITEMS.BRUTE, E.PAT_MULT, "Multipliers: 1, -1, 0.5, -0.5, 0, 0.75, -0.75 x max desync.\nStepped: 0, +1, -1, +2, -2 x brute step."), enable)
    dep(sld(gj, "brute_step", "Brute step", 5, 90, 30, "%d°", "Step of the Stepped pattern."), enable)
    dep(chk(gj, "brute_skip", "Skip offsets that just missed", true, "4.2: an effective offset (side x multiplier) that produced a resolver miss is not tried again for 20 s,\neven after the side flipped. When everything failed the list restarts at the entry that hit last."), enable)

    local gi = mk_group(tab, "Hints")
    dep(chk(gi, "body", "Body yaw hint", true, "Estimates lower/upper body yaw from hitbox geometry."), enable)
    dep(chk(gi, "freestand", "Freestanding hint", true, "Traces cover left/right of the head; freestanding AA hides toward cover."), enable)
    dep(chk(gi, "move_mem", "Movement memory", true, "Remembers the last movement yaw for a second after the enemy stops."), enable)
    dep(chk(gi, "move_dir", "Side from movement direction", true, "While running, the side is hinted by the movement direction relative to you."), enable)
    dep(chk(gi, "lc_detect", "Lag-compensation watch", true, "Teleports and simulation-time rewinds flag the target as LC-broken:\nmisses on it do not step the brute table and the rage assist treats it as unresolved."), enable)
    dep(chk(gi, "lc_hold", "Hold on LC break", true, "For 0.2 s after a lag-compensation break the yaw history is frozen and the last stable angles stay applied."), enable)

    local gl = mk_group(tab, "Learning")
    local feedback = dep(chk(gl, "feedback", "Hit / miss learning", true, "weapon_fire + player_hurt feedback drives side confidence and brute cycling."), enable)
    dep(sld(gl, "miss_win", "Miss window", 150, 1000, 350, "%d ms", "A shot without player_hurt within this window counts as a miss."), feedback)
    dep(sld(gl, "miss_tol", "Misses before step", 1, 3, 1, nil, "Consecutive resolver misses on a standing target before the brute index steps."), feedback)
    dep(chk(gl, "spread_blame", "Ignore spread misses", true, "Fallback heuristic: a spread cone wider than the head at that distance blames spread.\nSoft misses (spread, moving, airborne, off target) teach with half weight; hard ones (death, lost, lag comp) teach nothing."), feedback)
    dep(chk(gl, "body_partial", "Body hit = partial", true, "A body hit while body-aim was not forced gives reduced confidence and does not lock the brute index."), feedback)
    dep(chk(gl, "anti_ab", "Detect anti-bruteforce", true, "If the target flips his side after every hit, the next prediction flips with him."), feedback)
    dep(chk(gl, "cls_mem", "Side memory per AA class", true, "4.2: the confirmed side is remembered separately for static / sway / jitter / spin / random,\nso a target that switches anti-aim does not inherit the wrong side."), feedback)
    dep(chk(gl, "hint_learn", "Hint reliability learning", true, "Confirmed hits and resolver misses re-weight the body / freestanding / movement hints for this session."), feedback)
    dep(chk(gl, "flip_on_hurt", "Flip side when they hit you", false, "Invert the learned side of an enemy who just hit you."), feedback)
    dep(chk(gl, "persist", "Persist learning (db)", true, "Keeps learned sides per SteamID between sessions."), feedback)
end

function BUILD.rage()
    local chk, sld, cmb, key, mcb, btn, div, dep = W.chk, W.sld, W.cmb, W.key, W.mcb, W.btn, W.div, W.dep
    local tab = mk_tab("0x Rage")

    local gm = mk_group(tab, "Assist")
    local rb = chk(gm, "rb_enable", "Enable rage assist", true, "Drives hitchance, min damage, safepoint and hitboxes of your ragebot through config paths.\nEverything is restored on pause, death, weapon change and unload.")
    dep(cmb(gm, "preset", "Preset", ITEMS.PRESET, 2, "Balanced is universal, Aggressive fires sooner, Conservative wants more certainty.\nEditing a value switches the preset to Custom."), rb)
    dep(mcb(gm, "weapons", "Weapon groups", WPN.ITEMS, { true, true, true, true, true, false }, "The assist only touches the ragebot while one of the selected groups is active."), rb)
    dep(chk(gm, "pause_menu", "Pause while menu is open", true, "Your values are restored while the menu is open so you can edit the ragebot freely."), rb)

    local gh = mk_group(tab, "Headshot assist")
    local hs = dep(chk(gh, "hs_on", "Headshot assist", false, "4.2: when the resolver trusts its guess and the head is the better target, the ragebot is narrowed to the head:\nhitboxes become head-only, hitchance gets a bonus and (optionally) min damage is lifted above the body damage.\nNeeds the resolver. Never active on airborne / LC-breaking / unresolved targets."), rb)
    dep(sld(gh, "hs_trust", "Minimum resolver trust", 30, 95, 62, "%d%%", "Trust mixes side confidence, AA class, jitter prediction quality, hit / miss streaks and the brute index."), hs)
    dep(cmb(gh, "hs_need", "Go for the head when", ITEMS.HS_NEED, 2, "Head shot is lethal: only a killing head shot.\nHead beats body: lethal, or at least 25% more damage than the best body hitbox.\nWhenever trusted: trust alone decides."), hs)
    dep(mcb(gh, "hs_states", "Target states", ITEMS.HS_STATES, { true, true, true, false }, "The head is only forced while the target is in one of these states."), hs)
    dep(chk(gh, "hs_body_first", "Lethal body shot wins", true, "If one body shot kills, the body stays the target (safer than any head shot)."), hs)
    dep(sld(gh, "hs_hc", "Head hitchance bonus", 0, 25, 6, "+%d%%", "Added to the hitchance while the head is forced."), hs)
    dep(chk(gh, "hs_gate", "Damage gate", true, "Min damage is set just above the best body damage, so only a head shot satisfies it.\nUseful when no hitbox path was found. Never above the target's HP."), hs)
    key(gh, "k_head", "Force head", "While held: head-only hitboxes regardless of trust.")

    local gba = mk_group(tab, "Body-aim")
    local baim = dep(chk(gba, "baim_on", "Smart body-aim", true, "Body damage is traced; the head is removed from the hitboxes when the body is the better target."), rb)
    dep(chk(gba, "baim_lethal", "Body kills in 1 shot", true), baim)
    dep(chk(gba, "baim_2x", "Body kills in 2 shots", false, "Two body hits kill while one head hit would not (Deagle, pistols)."), baim)
    dep(sld(gba, "baim_margin", "Damage margin", 0, 30, 2, "%d HP"), baim)
    dep(chk(gba, "baim_hp_on", "Body at low HP", false), baim)
    dep(sld(gba, "baim_hp", "HP threshold", 1, 100, 40, "%d HP"), baim)
    dep(chk(gba, "baim_unres", "Body when unresolved", true, "Low-trust random / wide jitter targets, repeated misses, a deep brute index or an LC break get body-aim (reason RES / LC)."), baim)

    local gc = mk_group(tab, "Accuracy")
    local hc_on = dep(chk(gc, "hc_on", "Hitchance by state", true, "Own hitchance for standing, walking, running and ducking. 0 keeps yours."), rb)
    dep(sld(gc, "hc_stand", "Standing", 0, 100, 70, "%d%%"), hc_on)
    dep(sld(gc, "hc_slow", "Walking", 0, 100, 65, "%d%%"), hc_on)
    dep(sld(gc, "hc_move", "Running", 0, 100, 55, "%d%%"), hc_on)
    dep(sld(gc, "hc_duck", "Ducking", 0, 100, 72, "%d%%"), hc_on)
    div(gc, "Target")
    dep(sld(gc, "baim_fov", "Target search FOV", 5, 180, 60, "%d°", "Angle around the crosshair in which the target for corrections, damage cap, head and body decisions is searched."), rb)
    dep(sld(gc, "hc_tgt_air", "Target in air", -30, 30, -8, "%+d%%"), rb)
    dep(sld(gc, "hc_tgt_move", "Target running", -30, 30, 0, "%+d%%"), rb)
    dep(sld(gc, "unres_hc", "Target unresolved", -30, 30, 8, "%+d%%", "Hitchance adjustment when the resolver has little trust in its guess or the target breaks lag compensation."), rb)
    dep(sld(gc, "hc_cap", "Hitchance cap", 50, 100, 95, "%d%%", "Overall ceiling for the stacked bonuses (head, strict, unresolved). Your own base value is never lowered by it."), rb)
    dep(chk(gc, "dmg_cap", "Cap min damage at target HP", true, "A finishing shot is never blocked by a min damage above the target's HP."), rb)

    local ga = mk_group(tab, "Air")
    local air = dep(chk(ga, "air_on", "Jump optimizer", true, "Air hitchance, min damage and safepoint while you are airborne.\nSSG 08 reference: hitchance 65-78, damage 45-65."), rb)
    dep(sld(ga, "air_hc", "Air hitchance", 1, 100, 70, "%d%%"), air)
    dep(sld(ga, "air_dmg", "Air min damage", 1, 130, 50, "%d HP"), air)
    dep(chk(ga, "air_safe", "Air safepoint", true), air)
    local apex = dep(chk(ga, "apex_on", "Apex hitchance", true, "At the top of the jump the vertical speed is near zero and spread is minimal."), air)
    dep(sld(ga, "apex_hc", "Hitchance at apex", 1, 100, 58, "%d%%"), apex)
    dep(sld(ga, "apex_win", "Apex window", 10, 110, 42, "≤ %d u/s", "Apex while |vertical speed| is below this."), apex)
    div(ga, "Detection")
    dep(cmb(ga, "air_mode", "Air detection", ITEMS.AIR, 1, "Ground + vertical speed ignores stairs. Ground flag only reacts fastest.\nLanding prediction restores ground values a few ticks before touchdown (engine.simulate)."), rb)
    dep(sld(ga, "air_thr", "Vertical speed threshold", 5, 220, 22, "%d u/s"), rb)
    dep(sld(ga, "land_ticks", "Landing lead", 1, 8, 3, "%d ticks"), rb)

    local gb = mk_group(tab, "Binds")
    key(gb, "k_strict", "Strict · max accuracy", "While held: hitchance + Strict bonus, safepoint forced.")
    dep(sld(gb, "strict_bonus", "Strict hitchance bonus", 0, 40, 12, "+%d%%"), rb)
    key(gb, "k_baim", "Force body-aim", "While held: head is removed from the hitboxes. Wins over Force head.")
    key(gb, "k_dmg", "Min damage override", "While held: min damage = the value below.")
    dep(sld(gb, "dmg_bind_val", "Override min damage", 1, 130, 30, "%d HP"), rb)

    local gl = mk_group(tab, "Config link")
    UI.rb_status = W.lbl(gl, "Paths: scanning…")
    btn(gl, "rescan", "Rescan config", "rescan", "Find the ragebot paths in config.keys again.")
    btn(gl, "dump", "Dump paths to console", "dump", "Prints the discovered paths with their current values.")
    dep(chk(gl, "log_cfg", "Log config writes", true, "Prints path, old and new value of every config write to the Lua console."), rb)
end

function BUILD.visuals()
    local chk, sld, cmb, clr = W.chk, W.sld, W.cmb, W.clr
    local tab = mk_tab("0x Visuals")

    local g = mk_group(tab, "Players")
    chk(g, "overlay", "Player overlay", true, "AA class, side and desync above every tracked enemy.")
    cmb(g, "ov_style", "Overlay style", ITEMS.OVERLAY, 1, "Detailed adds confidence bar, hits / misses, brute index and pitch class.")
    chk(g, "yaw_lines", "Yaw lines", true, "Short lines from the head: dim = received yaw, accent = resolved yaw.")

    local gp = mk_group(tab, "Panel")
    chk(gp, "panel", "Status panel", true, "Movement state, live ragebot overrides and the crosshair target's AA.\nDrag it with the mouse while the menu is open.")
    sld(gp, "panel_x", "Panel X", 0, 100, 1, "%d%%")
    sld(gp, "panel_y", "Panel Y", 0, 100, 40, "%d%%")
    sld(gp, "panel_scale", "Panel scale", 80, 150, 100, "%d%%")
    chk(gp, "feed", "Event feed", true, "Hit / miss / brute events under the panel.")

    local gs = mk_group(tab, "Style")
    clr(gs, "accent", "Accent color", color(140, 148, 255, 255), "Overlay, lines, and panel accent.")
    chk(gs, "log_hits", "Log shots to console", false, "Prints every hit / miss with its classified reason to the Lua console.")
end

function BUILD.config()
    local chk, btn, lbl = W.chk, W.btn, W.lbl
    local tab = mk_tab("0x Config")

    local g = mk_group(tab, "Settings")
    chk(g, "persist_ui", "Remember settings (db)", true, "Stores this menu in data\\db and restores it on load.")
    chk(g, "notif", "Notifications", true)
    btn(g, "export", "Export settings", "export", "Writes data\\db\\0x_export.json, prints it to the console and copies it to the clipboard (Allow Insecure).")
    btn(g, "import_db", "Import data\\db\\0x_import.json", "import_db", "Loads a snapshot made by the web companion. Put the file into C:\\neverwin\\scripts\\data\\db.")
    UI.import_text = create(g, g.text, "import_text", "", "Snapshot (paste)", "")
    btn(g, "import_text", "Import pasted snapshot", "import_text", "Applies the JSON snapshot pasted into the field above.")
    btn(g, "reset_ui", "Reset settings to defaults", "reset_ui")

    local gd = mk_group(tab, "Data")
    UI.stats = lbl(gd, "tracked 0 · hits 0 · misses 0")
    btn(gd, "reset_learn", "Clear learned data", "reset_learn", "Forget every learned side and the hit / miss statistics.")

    local ga = mk_group(tab, "About")
    lbl(ga, META.name .. " v" .. META.version .. " " .. META.edition .. " · " .. META.credits)
    lbl(ga, "Tabs: Resolver · Rage · Visuals · Config")
end

local function build_menu()
    local order = { "resolver", "rage", "visuals", "config" }
    for i = 1, #order do
        local ok, err = pcall(BUILD[order[i]])
        if not ok then say("menu tab '" .. order[i] .. "' failed to build: " .. tostring(err)) end
    end
    MENU.built = true
end

-- ---------------------------------------------------------------- persistence
local CHANGED_DEFAULTS = { hs_on = true, log_cfg = true }   -- 4.5 changed these: old values are not imported

-- Manual paths (code constants + snapshot) as sanitized string lists.
function IO.clean_paths(src)
    local out = { hc = {}, dmg = {}, safe = {}, baim = {}, hitbox = {} }
    if type(src) ~= "table" then return out end
    for id, list in pairs(out) do
        local s = src[id]
        if type(s) == "string" then s = { s } end
        if type(s) == "table" then
            for i = 1, #s do
                local p = s[i]
                -- a snapshot is untrusted input: bounded length, printable ASCII only
                if type(p) == "string" and #p <= 160 then
                    p = U.trim(p)
                    if p ~= "" and #list < 16 and not s_find(p, "[^\32-\126]") then list[#list + 1] = p end
                end
            end
        end
    end
    return out
end

function IO.pack()
    local t = {}
    for i = 1, #ORDER do
        local r = REG[ORDER[i]]
        local k, v = r.kind, CFG[r.id]
        if k == "check" or k == "slider" or k == "combo" then
            t[r.id] = v
        elseif k == "color" and type(v) == "table" then
            t[r.id] = { r = floor(v.r), g = floor(v.g), b = floor(v.b), a = floor(v.a or 255) }
        elseif k == "multi" and type(v) == "table" then
            local m = {}
            for j = 1, #r.items do m[r.items[j]] = multi_on(v, j, r.items) end
            t[r.id] = m
        end
    end
    local paths, any = {}, false
    for id, list in pairs(PATHS_USER) do
        if #list > 0 then paths[id], any = list, true end
    end
    return { v = META.schema, ver = META.version, persist = CFG.persist_ui ~= false, s = t, paths = any and paths or nil }
end

function IO.save()
    local ok, res = pcall(db.save, META.db_settings, IO.pack())
    return ok and res ~= false
end

-- Writes a snapshot table into the menu. Returns the number of applied values or nil, reason.
function IO.apply(data, only_persist, skip)
    if type(data) ~= "table" or type(data.s) ~= "table" then return nil, "not a 0x snapshot" end
    local sv = tonumber(data.v)
    if sv and sv > META.schema then return nil, "snapshot was made by a newer 0x (schema " .. sv .. ")" end
    local n = 0
    PS.applying = true
    for id, v in pairs(data.s) do
        local r = REG[id]
        if r and r.kind ~= "key" and not (skip and skip[id]) and (not only_persist or id == "persist_ui") then
            local val = validate(r, v)
            if val ~= nil then
                write_el(r, val)
                n = n + 1
            end
        end
    end
    PS.applying = false
    if only_persist and REG.persist_ui then write_el(REG.persist_ui, false) end
    if type(data.paths) == "table" then PATHS_USER = IO.clean_paths(data.paths) end
    return n
end

function IO.load()
    local ok, data = pcall(db.load, META.db_settings, nil)
    local prev = false
    if not ok or type(data) ~= "table" or type(data.s) ~= "table" then
        ok, data = pcall(db.load, META.db_prev, nil)
        if not ok or type(data) ~= "table" or type(data.s) ~= "table" then return false end
        prev = true
    end
    -- The user opted out of remembering settings: keep only that choice.
    if data.persist == false then
        IO.apply(data, true)
        return false
    end
    local n = IO.apply(data, false, prev and CHANGED_DEFAULTS or nil) or 0
    if prev and n > 0 then
        say("imported " .. n .. " settings from the 4.x snapshot")
        SET.dirty, SET.dirty_t = true, -1e9
    end
    return n > 0
end

-- Applies an external snapshot (import) and makes it permanent.
function IO.import(data, origin)
    if type(data) ~= "table" then
        notify("Import failed (" .. origin .. "): not a JSON object")
        return false
    end
    local n, why = IO.apply(data, false)
    if not n then
        notify("Import failed (" .. origin .. "): " .. tostring(why))
        return false
    end
    refresh_all()
    PS.last = CFG.preset
    on_settings_changed(nil)
    SET.dirty, SET.dirty_t = true, -1e9
    if type(data.paths) == "table" then ACT.rescan() end
    notify(format("Imported %d settings from %s", n, origin))
    return true
end

function ACT.export()
    local snap = IO.pack()
    local ok, text = pcall(json.encode, snap)
    if not ok or type(text) ~= "string" then
        notify("Export failed: " .. tostring(text))
        return
    end
    local saved = safe(db.save, META.db_export, snap) == true
    say("snapshot: " .. text)
    local clip = false
    if safe(client.insecure) == true and utils and utils.clipboard_set then
        clip = pcall(utils.clipboard_set, text)
    end
    notify(format("Exported%s%s", saved and " to data\\db\\0x_export.json" or "", clip and " · copied to clipboard" or " · see console"))
end

function ACT.import_db()
    local ok, data = pcall(db.load, META.db_import, nil)
    if not ok or data == nil then
        notify("data\\db\\0x_import.json not found or not valid JSON")
        return
    end
    IO.import(data, "0x_import.json")
end

function ACT.import_text()
    local el = UI.import_text
    local s = el and not is_dummy(el) and safe(el.get, el) or nil
    if type(s) ~= "string" or U.trim(s) == "" then
        notify("Paste a snapshot into the field first")
        return
    end
    s = U.trim(s)
    if #s > META.import_max then
        notify(format("Snapshot rejected: %d bytes (limit %d)", #s, META.import_max))
        return
    end
    local brace = s_find(s, "{", 1, true)
    if brace and brace > 1 then s = s_sub(s, brace) end   -- tolerate a "0x:" style prefix
    local ok, data, err = pcall(json.decode, s)
    if not ok or data == nil then
        notify("Snapshot is not valid JSON: " .. tostring(ok and err or data))
        return
    end
    if IO.import(data, "pasted snapshot") then pcall(el.set, el, "") end
end

function ACT.reset_ui()
    PS.applying = true
    for i = 1, #ORDER do
        local r = REG[ORDER[i]]
        if r.kind ~= "key" then write_el(r, r.def) end
    end
    PS.applying = false
    refresh_all()
    PS.last = CFG.preset
    SET.dirty, SET.dirty_t = true, STATE.rt
    notify("Settings reset to defaults")
end

-- ============================================================================
--  RESOLVER MODULE (0x_resolver.lua, loaded with require)
--  If the module is missing or broken the stub below keeps everything else running.
-- ============================================================================
local function resolver_stub()
    local stub = {
        records = {}, by_pawn = {}, pending = {}, stats = {}, flipped = {}, focus = nil,
        ack = { n = 0, t = -1e9 }, ack_mode = "n/a", write_ok = nil, insecure = false, stub = true,
        unresolved = function() return false end,
        trust = function() return 0 end,
        can_write = function() return false end,
        ack_live = function() return false end,
    }
    local noop = function() end
    for _, name in pairs({ "frame", "cmd_fix", "sample_spread", "on_weapon_fire", "on_player_hurt", "on_player_death",
                           "on_round_start", "on_level_init", "on_level_shutdown", "on_aim_ack", "store_load", "store_save" }) do
        stub[name] = noop
    end
    return stub
end

local RESOLVER_NAMES = { META.module, "local/" .. META.module, "scripts/" .. META.module }

local function resolver_load(ctx)
    local err
    for _, name in ipairs(RESOLVER_NAMES) do
        local ok, factory = pcall(require, name)
        if ok and type(factory) == "function" then
            local ok2, res = pcall(factory, ctx)
            if ok2 and type(res) == "table" then return res end
            say("resolver module failed to initialise: " .. tostring(res))
            return nil
        end
        err = err or factory
    end
    say("resolver module '" .. META.module .. "' not loaded: " .. tostring(err))
    return nil
end

local RES = resolver_load({
    META = META, K = K, E = E, CFG = CFG, UI = UI, STATE = STATE, U = U, RB = RB, WPN = WPN, ACT = ACT,
    safe = safe, clamp = clamp, lerp = lerp, round = round, sign = sign, normalize = normalize,
    say = say, notify = notify, report = report, bind_on = bind_on, get_weapon_info = get_weapon_info,
    feed = function(kind, text) VIS.push(kind, text) end,
}) or resolver_stub()

-- ============================================================================
--  RAGE ASSIST
--  There is no ragebot module in the API, so values are read and written through
--  config.get / config.set. Paths are discovered from config.keys; originals are
--  journaled in db and returned when the assist stands down.
-- ============================================================================
RB.tick_n, RB.cm_t, RB.paint_t, RB.hk_t, RB.store_t = 0, -1e9, -1e9, -1e9, 0
RB.air_ticks, RB.land_soon, RB.sim_fail, RB.sim_disabled, RB.g_tick = 0, false, 0, false, K.GRAVITY * 0.015625
RB.state, RB.wgroup, RB.waddr, RB.wtick, RB.eval_at = nil, nil, nil, -1e9, 0
RB.t_hp, RB.t_air, RB.t_move, RB.t_addr, RB.t_unres = nil, false, false, nil, false
RB.baim_reason, RB.baim_until, RB.base_hc, RB.base_dmg = nil, 0, nil, nil
RB.hc, RB.dmg, RB.safe, RB.baim, RB.strict, RB.pub_thp = nil, nil, false, nil, false, nil
RB.touched, RB.paused, RB.in_game = false, false, true
RB.boot_status = "—"

local function is_head_name(x)
    if type(x) ~= "string" then return false end
    local l = s_lower(x)
    return s_find(l, "head", 1, true) ~= nil and s_find(l, "ahead", 1, true) == nil
end

-- Classifies a multi-select hitbox table returned by config.get:
--   "bool_array" : {true, true, ...} (index 1 = Head)
--   "str_array"  : {"Head", "Chest", ...}
--   "map"        : {Head = true, Chest = false, ...}
local function hitbox_kind(v)
    if type(v) ~= "table" then return nil end
    local n, total = #v, 0
    for _ in pairs(v) do total = total + 1 end
    if total == 0 then return nil end
    if n > 0 and total == n then
        local t = type(v[1])
        if t == "boolean" and n >= 2 then
            for i = 2, n do
                if type(v[i]) ~= "boolean" then return nil end
            end
            return "bool_array"
        elseif t == "string" then
            for i = 2, n do
                if type(v[i]) ~= "string" then return nil end
            end
            return "str_array"
        end
        return nil
    end
    if n == 0 then
        for k, x in pairs(v) do
            if type(k) ~= "string" or type(x) ~= "boolean" then return nil end
        end
        return "map"
    end
    return nil
end

-- Removes the head entry from a hitbox multi-select value. Returns the new value, the
-- original (head was not enabled) or (nil, reason) when unsupported / no body hitbox remains.
local function strip_head(v)
    local kind = hitbox_kind(v)
    if not kind then return nil, "unsupported" end
    if kind == "bool_array" then
        if not v[1] then return v end
        local out, enabled = { false }, 0
        for i = 2, #v do
            local x = v[i]
            out[i] = x
            if x then enabled = enabled + 1 end
        end
        if enabled == 0 then return nil, "empty" end
        return out
    elseif kind == "str_array" then
        local out, enabled, changed = {}, 0, false
        for i = 1, #v do
            local x = v[i]
            if is_head_name(x) then
                changed = true
            else
                out[#out + 1] = x
                enabled = enabled + 1
            end
        end
        if not changed then return v end
        if enabled == 0 then return nil, "empty" end
        return out
    end
    local out, enabled, changed = {}, 0, false
    for k, x in pairs(v) do
        if is_head_name(k) and x then
            out[k] = false
            changed = true
        else
            out[k] = x
            if x then enabled = enabled + 1 end
        end
    end
    if not changed then return v end
    if enabled == 0 then return nil, "empty" end
    return out
end

local function fmt_v(v)
    local tv = type(v)
    if tv == "number" then
        if v == floor(v) then return format("%d", v) end
        return format("%.2f", v)
    elseif tv == "table" then
        local parts, n, arr_n = {}, 0, #v
        if arr_n > 0 then
            for i = 1, arr_n do
                n = n + 1
                if n > 8 then parts[#parts + 1] = ".." break end
                parts[#parts + 1] = tostring(v[i])
            end
        else
            for k, x in pairs(v) do
                n = n + 1
                if n > 8 then parts[#parts + 1] = ".." break end
                parts[#parts + 1] = tostring(k) .. "=" .. tostring(x)
            end
        end
        return "{" .. tconcat(parts, ",") .. "}"
    end
    return tostring(v)
end

local function cfg_get(path)
    local ok, v = pcall(config.get, path)
    if ok then return v end
    return nil
end

local function cfg_set(path, v)
    local ok, r = pcall(config.set, path, v)
    return ok and r ~= false
end

-- ---------------------------------------------------------------- journal
-- data: originals of paths currently overridden (or whose restore failed). disk: copy of the
-- file. The file is rewritten when an entry is missing (immediately) or stale (lazily).
Journal.data, Journal.disk = {}, {}
Journal.add_dirty, Journal.rm_dirty, Journal.rm_t = false, false, 0

function Journal.add(path, orig)
    local v = U.copy(orig)
    Journal.data[path] = v
    if not U.same(Journal.disk[path], v) then Journal.add_dirty = true end
end

function Journal.remove(path)
    if Journal.data[path] == nil then return end
    Journal.data[path] = nil
    if Journal.disk[path] ~= nil then Journal.rm_dirty, Journal.rm_t = true, STATE.rt end
end

function Journal.missing()
    for k, v in pairs(Journal.data) do
        if not U.same(Journal.disk[k], v) then return true end
    end
    return false
end

function Journal.stale()
    for k in pairs(Journal.disk) do
        if Journal.data[k] == nil then return true end
    end
    return false
end

function Journal.flush(force)
    local need = false
    if Journal.add_dirty then
        need = Journal.missing()
        if not need then Journal.add_dirty = false end
    end
    if not need and Journal.rm_dirty and (force or STATE.rt - Journal.rm_t >= K.JOURNAL_LAZY) then
        need = Journal.stale()
        if not need then Journal.rm_dirty = false end
    end
    if not need then return end
    if not force and STATE.rt - SET.io_t < K.IO_RETRY then return end
    local ok, res = pcall(db.save, META.db_journal, Journal.data)
    if ok and res ~= false then
        local disk = {}
        for k, v in pairs(Journal.data) do disk[k] = U.copy(v) end
        Journal.disk = disk
        Journal.add_dirty, Journal.rm_dirty = false, false
    else
        SET.io_t = STATE.rt
    end
end

-- Returns config values left in the journal by a crash. What cannot be restored stays in
-- the journal: the next capture of that path takes its original from there.
function Journal.restore()
    local ok, saved = pcall(db.load, META.db_journal, nil)
    if not ok or type(saved) ~= "table" then return 0 end
    local n, any = 0, false
    for path, val in pairs(saved) do
        if type(path) == "string" and val ~= nil and val ~= json.null then
            any = true
            Journal.disk[path] = U.copy(val)
            local cur = cfg_get(path)
            if cur ~= nil and type(cur) == type(val) and not U.same(cur, val) then
                if cfg_set(path, val) then
                    n = n + 1
                else
                    Journal.data[path] = U.copy(val)
                end
            end
        end
    end
    if any then Journal.rm_dirty, Journal.rm_t = true, -1e9 end
    return n
end

-- ---------------------------------------------------------------- config binding
local NONE = {}          -- "original not captured"
local TRANSFORM = {}     -- "value derived from the original" (flags, lists)
Bind.HEAD = {}           -- "hitbox list narrowed to the head" (headshot assist)

local GENERIC_EXCLUDE = {
    "colou?r", "visual", "%f[%w]esp%f[%W]", "chams", "glow", "indicator", "draw", "show",
    "%f[%w]logs?%f[%W]", "legit", "trigger", "%f[%w]keys?%f[%W]", "hotkey", "bind", "sound",
    "notif", "%f[%w]hud%f[%W]", "font", "preview", "widget", "overr", "%f[%w]ovr%f[%W]",
}

local ORDER_P = { "hc", "dmg", "safe", "baim", "hitbox" }
local SL = {
    hc = { tag = "HC", title = "Hitchance",
        patterns = { "hit[%s_%.%-]?chance" }, exclude = {},
        ok = function(v) return type(v) == "number" and v >= 0 and v <= 100 end },
    dmg = { tag = "DMG", title = "Min damage",
        patterns = { "min[%s_%.%-]?dam", "min[%s_%.%-]?dmg" }, exclude = {},
        ok = function(v) return type(v) == "number" and v >= 0 and v <= 300 end },
    safe = { tag = "SAFE", title = "Safepoint",
        patterns = { "safe[%s_%.%-]?point" },
        exclude = { "unsafe", "multi", "hitbox", "limit", "min" },
        ok = function(v) return type(v) == "boolean" or (type(v) == "number" and v >= 0 and v <= 10) end },
    baim = { tag = "BAIM", title = "Body-aim",
        patterns = { "body[%s_%.%-]?aim", "baim", "prefer[%s_%.%-]?body", "force[%s_%.%-]?body" },
        exclude = { "lethal", "disabl", "hp", "health", "dam", "dmg", "condition", "unsafe",
                    "after", "miss", "shot", "min", "max" },
        ok = function(v) return type(v) == "boolean" end },
    hitbox = { tag = "HITBOX", title = "Hitboxes",
        patterns = { "hit[%s_%.%-]?box" },
        exclude = { "point", "scale", "prior", "debug", "history", "backtrack" },
        ok = function(v) return hitbox_kind(v) ~= nil end },
}
for i = 1, #ORDER_P do
    local sl = SL[ORDER_P[i]]
    sl.id, sl.recs, sl.n = ORDER_P[i], {}, 0
    sl.w, sl.g, sl.force, sl.custom, sl.live, sl.full = nil, 0, false, false, 0, false
end
local CLAIMED = {}       -- path -> parameter id: one path serves one parameter

SL.safe.transform = function(orig)
    if type(orig) == "boolean" then return true end
    if type(orig) == "number" then return SAFE_COMBO_VALUE end
    return nil
end
SL.baim.transform = function(orig)
    if type(orig) == "boolean" then return true end
    return nil
end
SL.hitbox.transform = function(orig) return strip_head(orig) end

-- Path tags: which weapon group a path belongs to. Untagged paths apply to every group.
local PATH_TAGS = {
    { 1, { "ssg", "scout" } },
    { 2, { "awp" } },
    { 3, { "autosnip", "auto[%s_%.%-]snip", "scar", "g3sg1", "%f[%w]auto%f[%W]" } },
    { 4, { "deagle", "revolver", "%f[%w]r8%f[%W]", "heavy" } },
    { 5, { "pistol" } },
    { 6, { "rifle", "smg", "shotgun", "machine", "%f[%w]other%f[%W]" } },
}

function Bind.tags_for(low)
    local tags
    for i = 1, #PATH_TAGS do
        if U.any_match(low, PATH_TAGS[i][2]) then
            tags = tags or {}
            tags[PATH_TAGS[i][1]] = true
        end
    end
    if tags and tags[4] and tags[5] and s_find(low, "heavy", 1, true) then tags[5] = nil end
    return tags
end

function Bind.add_path(sl, path, forced)
    local owner = CLAIMED[path]
    if owner then
        if forced and owner ~= sl.id then
            say(sl.title .. ": path '" .. path .. "' is already used by '" .. SL[owner].title .. "'")
        end
        return false
    end
    local v = cfg_get(path)
    if v == nil then
        if forced then say(sl.title .. ": path '" .. path .. "' not found in config") end
        return false
    end
    if not sl.ok(v) then
        if forced then say(sl.title .. ": path '" .. path .. "' has an unsupported type (" .. type(v) .. ")") end
        return false
    end
    CLAIMED[path] = sl.id
    sl.n = sl.n + 1
    -- orig: user's value (NONE until touched); cur: what config holds now; want: last desired
    -- value; eff: whether config accepted it.
    sl.recs[sl.n] = { path = path, tags = Bind.tags_for(s_lower(path)), orig = NONE, cur = nil, want = nil,
                      eff = false, sup = true, bad = 0, mism = 0, dead = false, warned = false, ro = false }
    return true
end

function Bind.fail(sl, rec, why)
    rec.bad = rec.bad + 1
    if rec.bad < K.BAD_LIMIT then
        sl.force = true
    elseif not rec.dead then
        rec.dead = true
        say("path disabled until rescan (" .. why .. "): " .. rec.path)
    end
end

-- Returns the user's value. true = config is guaranteed to hold the original.
function Bind.restore(sl, rec, final)
    if rec.orig == NONE then return true end
    if rec.dead and not final then return false end
    if not U.same(rec.cur, rec.orig) then
        if not cfg_set(rec.path, rec.orig) then
            Bind.fail(sl, rec, "restore failed, original stays in the journal")
            return false
        end
        if CFG.log_cfg then say(format("%s <- %s (restore)", rec.path, fmt_v(rec.orig))) end
    end
    rec.orig, rec.cur, rec.want, rec.eff = NONE, nil, nil, false
    Journal.remove(rec.path)
    return true
end

-- Restores everything. A journal entry disappears only together with a successful restore.
function Bind.release(final)
    Bind.clear_pub()
    if not RB.touched and not final then return end
    local pending = false
    for i = 1, #ORDER_P do
        local sl = SL[ORDER_P[i]]
        local recs = sl.recs
        for j = 1, sl.n do
            local rec = recs[j]
            if rec.orig ~= NONE and not Bind.restore(sl, rec, final) and not rec.dead then pending = true end
        end
        sl.w, sl.g, sl.force, sl.live = nil, 0, false, 0
    end
    RB.touched = pending
end

function Bind.scan()
    Bind.release(true)
    for k in pairs(CLAIMED) do CLAIMED[k] = nil end
    for i = 1, #ORDER_P do
        local sl = SL[ORDER_P[i]]
        sl.recs, sl.n, sl.w, sl.g, sl.force, sl.custom, sl.live, sl.full = {}, 0, nil, 0, false, false, 0, false
        local lists = { CUSTOM_PATHS[sl.id], PATHS_USER[sl.id] }
        for li = 1, 2 do
            local list = lists[li]
            if type(list) == "table" then
                for j = 1, #list do
                    if type(list[j]) == "string" then
                        sl.custom = true
                        Bind.add_path(sl, list[j], true)
                    end
                end
            end
        end
    end
    RB.eval_at = 0
    local ok, keys = pcall(config.keys)
    if not ok or type(keys) ~= "table" then
        say("config.keys unavailable: " .. tostring(keys) .. ". Set manual paths (CUSTOM_PATHS or a snapshot).")
        return false
    end
    for i = 1, #keys do
        local path = keys[i]
        if type(path) == "string" and not CLAIMED[path] then
            local low = s_lower(path)
            local excluded = nil
            for j = 1, #ORDER_P do
                local sl = SL[ORDER_P[j]]
                if not sl.custom and U.any_match(low, sl.patterns) then
                    if excluded == nil then excluded = U.any_match(low, GENERIC_EXCLUDE) end
                    if excluded then break end
                    if not U.any_match(low, sl.exclude) then
                        if sl.n < K.MAX_CANDS then
                            if Bind.add_path(sl, path, false) then break end
                        elseif not sl.full then
                            sl.full = true
                            say(format("%s: more than %d paths found, extras skipped. Use manual paths.", sl.title, K.MAX_CANDS))
                        end
                    end
                end
            end
        end
    end
    return true
end

function Bind.total()
    local n = 0
    for i = 1, #ORDER_P do n = n + SL[ORDER_P[i]].n end
    return n
end

function Bind.summary()
    local p = {}
    for i = 1, #ORDER_P do
        local sl = SL[ORDER_P[i]]
        p[#p + 1] = format("%s %d", sl.tag, sl.n)
    end
    return tconcat(p, " · ")
end

function Bind.dump()
    say("---- config paths found by 0x ----")
    for i = 1, #ORDER_P do
        local sl = SL[ORDER_P[i]]
        say(format("%s: %d found%s", sl.title, sl.n, sl.custom and " (manual)" or ""))
        for j = 1, sl.n do
            local r = sl.recs[j]
            local tg = "all"
            if r.tags then
                local t = {}
                for g in pairs(r.tags) do t[#t + 1] = tostring(g) end
                tsort(t)
                tg = tconcat(t, ",")
            end
            say(format("   %s = %s  [weapon groups: %s]%s%s", r.path, fmt_v(cfg_get(r.path)), tg,
                r.dead and "  DISABLED" or "", r.ro and "  READ-ONLY" or ""))
        end
    end
end

-- Original numeric value of the first matching path (Strict and damage cap).
function Bind.base(sl, group)
    if not group then return nil end
    for i = 1, sl.n do
        local r = sl.recs[i]
        if not r.dead and (r.tags == nil or r.tags[group]) then
            local v = r.orig
            if v == NONE then v = cfg_get(r.path) end
            if type(v) == "number" then return v end
        end
    end
    return nil
end

-- Writes the desired value (number / value / TRANSFORM). true = config holds it.
function Bind.push(sl, rec, target)
    if rec.dead then return false end
    if rec.orig == NONE then
        local cur = cfg_get(rec.path)
        if cur == nil then
            Bind.fail(sl, rec, "path no longer readable")
            return false
        end
        local pending = Journal.data[rec.path]
        if pending ~= nil and type(pending) == type(cur) then
            rec.orig = U.copy(pending)            -- previous restore failed: the real original is in the journal
        else
            rec.orig = U.copy(cur)
            Journal.add(rec.path, rec.orig)
        end
        rec.cur, rec.want, rec.eff = U.copy(cur), nil, false
        RB.touched = true
    end

    local val, supported = target, true
    if target == TRANSFORM or target == Bind.HEAD then
        local fn = (target == Bind.HEAD) and sl.head_only or sl.transform
        local reason
        if fn then
            val, reason = fn(rec.orig)
        else
            val, reason = nil, "unsupported"
        end
        if val == nil then
            if reason ~= "empty" and reason ~= "no_head" and not rec.warned then
                rec.warned = true
                say("value format not supported, path skipped: " .. rec.path .. " = " .. fmt_v(rec.orig))
            end
            val, supported = rec.orig, false
        end
    end
    if rec.want ~= nil and rec.sup == supported and U.same(rec.want, val) then return rec.eff end

    local eff
    if U.same(val, rec.orig) then
        if not U.same(rec.cur, rec.orig) then
            if not cfg_set(rec.path, rec.orig) then
                Bind.fail(sl, rec, "write rejected")
                return false
            end
            if CFG.log_cfg then say(format("%s <- %s (equals yours)", rec.path, fmt_v(rec.orig))) end
            rec.cur = U.copy(rec.orig)
        end
        eff = supported
    elseif cfg_set(rec.path, val) then
        local echo = cfg_get(rec.path)             -- config may clamp or round the value
        if echo == nil then echo = val end
        rec.cur, rec.bad = U.copy(echo), 0
        eff = not U.same(echo, rec.orig)
        if not eff and not rec.ro then
            rec.ro = true
            say("write accepted but the value did not change: " .. rec.path .. " (wanted " .. fmt_v(val) .. ")")
        end
        if CFG.log_cfg then say(format("%s: %s -> %s", rec.path, fmt_v(rec.orig), fmt_v(echo))) end
    else
        Bind.fail(sl, rec, "write rejected")
        return false
    end
    rec.want, rec.eff, rec.sup = U.copy(val), eff, supported
    return eff
end

function Bind.apply(sl, want, group)
    if sl.n == 0 then return end
    if want == nil then group = 0 end
    if sl.w == want and sl.g == group and not sl.force then return end
    sl.w, sl.g, sl.force = want, group, false
    local recs, live = sl.recs, 0
    for i = 1, sl.n do
        local rec = recs[i]
        if want ~= nil and (rec.tags == nil or rec.tags[group]) then
            if Bind.push(sl, rec, want) then live = live + 1 end
        elseif rec.orig ~= NONE then
            Bind.restore(sl, rec, false)
        end
    end
    sl.live = live
end

-- Cross-check: a value changed by the user or by other code becomes the new original.
function Bind.verify()
    for i = 1, #ORDER_P do
        local sl = SL[ORDER_P[i]]
        local recs = sl.recs
        for j = 1, sl.n do
            local rec = recs[j]
            if rec.orig ~= NONE and not rec.dead then
                local cur = cfg_get(rec.path)
                if cur ~= nil then
                    if U.same(cur, rec.cur) then
                        rec.mism = 0
                    else
                        if not STATE.menu_open then rec.mism = rec.mism + 1 end
                        if rec.mism > K.MISM_LIMIT then
                            rec.dead = true
                            rec.orig, rec.cur, rec.want, rec.eff = NONE, nil, nil, false
                            Journal.remove(rec.path)
                            say("path disabled until rescan (constantly changed by other code): " .. rec.path)
                        else
                            rec.orig, rec.cur, rec.want, rec.eff = U.copy(cur), U.copy(cur), nil, false
                            Journal.add(rec.path, rec.orig)
                            sl.force = true
                        end
                    end
                end
            end
        end
    end
end

-- ---------------------------------------------------------------- logic
local HB = { cache = {}, n = 0 }
local CAND = { list = {}, n = 0 }

function RB.reset()
    HB.cache, HB.n = {}, 0
    for i = 1, CAND.n do CAND.list[i].pawn = nil end
    CAND.n = 0
    RB.waddr, RB.wgroup, RB.state = nil, nil, nil
    RB.clear_target()
    RB.baim_reason, RB.baim_until = nil, 0
    RB.hs_reason, RB.hs_until = nil, 0
    RB.base_hc, RB.base_dmg = nil, nil
    RB.land_soon, RB.air_ticks = false, 0
    RB.eval_at = 0
    VIS.dirty = true
end

function RB.classify(w)
    local ok, info = pcall(w.weapon_info, w)
    if not ok or type(info) ~= "table" then return nil end
    if info.gun == false then return nil end
    local def = tonumber(info.def)
    if def and WPN.BY_DEF[def] then return WPN.BY_DEF[def] end
    if def and WPN.NON_GUN_DEF[def] then return nil end
    local name = type(info.name) == "string" and s_lower(info.name) or ""
    for i = 1, #WPN.BY_NAME do
        if s_find(name, WPN.BY_NAME[i][1], 1, true) then return WPN.BY_NAME[i][2] end
    end
    if WPN.non_gun_name(name) then return nil end
    return 6
end

function RB.weapon(lp)
    local w = safe(lp.weapon, lp)
    if not w then
        if RB.wgroup ~= nil then RB.eval_at, VIS.dirty = 0, true end
        RB.wgroup, RB.waddr = nil, nil
        return
    end
    local addr = safe(w.address, w)
    if not addr then return end
    if addr ~= RB.waddr or RB.tick_n - RB.wtick >= K.WEAPON_TICKS then
        RB.waddr, RB.wtick = addr, RB.tick_n
        local g = RB.classify(w)
        if g ~= RB.wgroup then
            RB.wgroup = g
            RB.eval_at = 0
            VIS.dirty = true
        end
    end
end

-- Landing prediction: will we touch the ground within land_ticks ticks? (createmove only)
function RB.predict()
    local ok, sim = pcall(engine.simulate, CFG.land_ticks)
    if not ok or type(sim) ~= "table" then
        RB.sim_fail = RB.sim_fail + 1
        if RB.sim_fail >= 3 and not RB.sim_disabled then
            RB.sim_disabled = true
            notify("engine.simulate unavailable: landing prediction falls back to 'Ground + vertical speed'")
        end
        return
    end
    RB.sim_fail = 0
    for i = 1, #sim do
        local s = sim[i]
        if type(s) == "table" and s.valid ~= false and (s.landed or s.on_ground) then
            RB.land_soon = true
            return
        end
    end
end

-- Local movement state. Runs every createmove (shot bookkeeping needs it even when the
-- assist is off); the landing simulation only runs when the assist uses it.
function RB.movement(lp, cmd)
    local vel = safe(lp.velocity, lp)
    local vx, vy, vz = 0, 0, 0
    if vel then vx, vy, vz = vel.x or 0, vel.y or 0, vel.z or 0 end
    local speed = sqrt(vx * vx + vy * vy)
    local grounded = safe(lp.on_ground, lp) ~= false
    if grounded then
        RB.air_ticks, RB.land_soon = 0, false
    else
        RB.air_ticks = RB.air_ticks + 1
    end
    local mode = CFG.air_mode
    if mode == 3 and RB.sim_disabled then mode = 1 end
    local air = false
    if not grounded then
        if mode == 2 then
            air = true
        else
            air = RB.air_ticks >= 2 and (abs(vz) >= CFG.air_thr or RB.air_ticks >= 10)
        end
    end
    if air and mode == 3 and CFG.rb_enable then
        -- While rising, landing within land_ticks is impossible and the simulation is skipped.
        if not RB.land_soon and vz <= RB.g_tick * CFG.land_ticks + K.SIM_MARGIN then RB.predict() end
        if RB.land_soon then air = false end
    end
    local st
    if air then
        st = (CFG.apex_on and abs(vz) <= CFG.apex_win) and ST.APEX or ST.AIR
    elseif band(safe(lp.flags, lp) or 0, K.FL_DUCKING) ~= 0 then
        st = ST.DUCK
    elseif speed < K.MOVE_EPS then
        st = ST.STAND
    elseif cmd:has(K.BTN_SPEED) then
        st = ST.SLOW
    else
        st = ST.MOVE
    end
    STATE.lp_air = not grounded
    STATE.lp_moving = speed >= K.MOVE_EPS
    RB.mstate = st
end

local function hg_from_name(s)
    if type(s) ~= "string" then return 0 end
    local l = s_lower(s)
    if s_find(l, "head", 1, true) then return K.HG_HEAD end
    if s_find(l, "chest", 1, true) then return K.HG_CHEST end
    if s_find(l, "stomach", 1, true) then return K.HG_STOMACH end
    return 0
end

-- Head / chest / stomach hitbox indices from pawn:hitboxes(), cached per pawn.
function RB.hitbox_ids(pawn)
    local addr = safe(pawn.address, pawn)
    if not addr then return nil end
    local c = HB.cache[addr]
    if c and RB.tick_n - c.t < K.HB_TTL then return c end
    local ok, list = pcall(pawn.hitboxes, pawn)
    if not ok or type(list) ~= "table" then return nil end
    local body, head, got = {}, nil, {}
    for i = 1, #list do
        local hb = list[i]
        if type(hb) == "table" and hb.index ~= nil then
            local g = hb.group
            if type(g) ~= "number" then g = hg_from_name(hb.group_name or g) end
            if g == K.HG_HEAD then
                if not head then head = { index = hb.index, group = g } end
            elseif (g == K.HG_CHEST or g == K.HG_STOMACH) and not got[g] then
                got[g] = true
                body[#body + 1] = { index = hb.index, group = g }
            end
        end
    end
    if c == nil then
        if HB.n >= K.HB_MAX then HB.cache, HB.n = {}, 0 end
        HB.n = HB.n + 1
    end
    c = { t = RB.tick_n, body = body, head = head }
    HB.cache[addr] = c
    return c
end

function RB.dmg_at(eye, pawn, entry)
    local pos = safe(pawn.hitbox, pawn, entry.index)
    if not pos then return 0 end
    local ok, d = pcall(trace.damage, pawn, pos, entry.group, eye)
    if ok and type(d) == "number" then return d end
    return 0
end

function RB.set_pub(k, v)
    if RB[k] ~= v then
        RB[k] = v
        VIS.dirty = true
    end
end

-- Not active this tick: restore the ragebot values; the panel hides the state.
function RB.stand_down(keep_state)
    if not keep_state and RB.state ~= nil then
        RB.state = nil
        VIS.dirty = true
    end
    RB.eval_at = 0
    Bind.release(false)
end

function RB.set_status(txt)
    if UI.rb_status and not is_dummy(UI.rb_status) then pcall(UI.rb_status.set, UI.rb_status, "Paths: " .. txt) end
end

function ACT.rescan()
    local ok = Bind.scan()
    local txt = ok and Bind.summary() or "config.keys unavailable"
    RB.set_status(txt)
    notify("Found: " .. txt)
end

function ACT.dump() Bind.dump() end

-- Per-tick entry point (createmove). lp is alive when given.
function RB.tick(cmd, lp)
    RB.cm_t = STATE.rt
    RB.tick_n = RB.tick_n + 1

    if not CFG.rb_enable then
        if RB.paused then RB.paused, VIS.dirty = false, true end
        RB.stand_down(false)
        return
    end
    if STATE.menu_open and CFG.pause_menu then
        if not RB.paused then RB.paused, VIS.dirty = true, true end
        RB.stand_down(true)
        return
    end
    if RB.paused then RB.paused, VIS.dirty = false, true end

    if not lp then
        if RB.state ~= nil or RB.wgroup ~= nil then RB.reset() end
        RB.stand_down(false)
        return
    end

    RB.weapon(lp)
    local grp = RB.wgroup
    if not grp or not multi_on(CFG.weapons, grp, WPN.ITEMS) then
        RB.stand_down(false)
        return
    end

    if RB.mstate ~= RB.state then
        RB.state = RB.mstate
        VIS.dirty = true
    end
    if RB.tick_n >= RB.eval_at then
        RB.eval_at = RB.tick_n + K.EVAL_TICKS
        RB.eval_targets(lp)
    end
    RB.decide(grp)
    if RB.tick_n % K.VERIFY_TICKS == 0 then Bind.verify() end
end

-- Once per second: everything that does not have to happen every frame.
function RB.housekeeping(now)
    RB.hk_t = now
    local ok, ig = pcall(engine.in_game)
    RB.in_game = (not ok) or ig ~= false
    local sw, sh = render.screen_size()
    if type(sw) == "number" and type(sh) == "number" and sw > 0 and sh > 0 then STATE.sw, STATE.sh = sw, sh end
    if SET.dirty and now - SET.dirty_t >= K.SAVE_DELAY then
        if IO.save() then SET.dirty = false else SET.dirty_t = now + K.IO_RETRY end
    end
    Journal.flush(false)
    if RES.store_dirty and now - RB.store_t > 30 then        -- crash safety for learned sides
        RB.store_t = now
        RES.store_save(false)
    end
    for _, m in pairs(MODS) do
        if m.strikes > 0 and now - m.strike_t > K.ERR_FORGIVE then m.strikes = 0 end
    end
end

-- Background tasks run from paint; createmove takes over if paint goes silent.
function RB.background(now)
    MENU.poll(now)
    -- menu_toggled can be missed: cross-check with input.menu_open after a short grace period
    if now - STATE.menu_evt_t > 0.25 and now - STATE.menu_poll_t > 0.25 then
        STATE.menu_poll_t = now
        local ok, open = pcall(input.menu_open)
        if ok and type(open) == "boolean" and open ~= STATE.menu_open then
            RB.on_menu_toggled(open, true)
        end
    end
    if Journal.add_dirty then Journal.flush(false) end
    if now - RB.hk_t >= K.HK_INTERVAL then RB.housekeeping(now) end
end

function RB.on_menu_toggled(open, polled)
    STATE.menu_open = open and true or false
    if not polled then STATE.menu_evt_t = STATE.rt end
    if STATE.menu_open then
        if CFG.pause_menu and CFG.rb_enable then
            RB.paused, VIS.dirty = true, true
            Bind.release(false)
        end
        Journal.flush(true)
    end
end

function RB.on_level()
    Bind.release(true)
    RB.reset()
    Journal.flush(true)
end

function RB.on_unload()
    Bind.release(true)
    Journal.flush(true)
end

-- ============================================================================
--  RAGE ASSIST · 4.2: target evaluation, headshot assist, decision
-- ============================================================================
RB.hs_reason, RB.hs_until, RB.head = nil, 0, nil
RB.t_bd, RB.t_hd, RB.t_state, RB.t_trust = 0, 0, 1, 0
-- Keeps only the head entries of a hitbox multi-select value. Returns the new value, the
-- original (already head-only) or (nil, reason) when unsupported / the user has no head enabled.
function RB.keep_head(v)
    local kind = hitbox_kind(v)
    if not kind then return nil, "unsupported" end
    if kind == "bool_array" then
        if not v[1] then return nil, "no_head" end
        local others = 0
        for i = 2, #v do
            if v[i] then others = others + 1 end
        end
        if others == 0 then return v end
        local out = { true }
        for i = 2, #v do out[i] = false end
        return out
    elseif kind == "str_array" then
        local out, heads, others = {}, 0, 0
        for i = 1, #v do
            local x = v[i]
            if is_head_name(x) then
                out[#out + 1] = x
                heads = heads + 1
            else
                others = others + 1
            end
        end
        if heads == 0 then return nil, "no_head" end
        if others == 0 then return v end
        return out
    end
    local out, heads, others = {}, 0, 0
    for k, x in pairs(v) do
        if is_head_name(k) then
            out[k] = x
            if x then heads = heads + 1 end
        else
            out[k] = false
            if x then others = others + 1 end
        end
    end
    if heads == 0 then return nil, "no_head" end
    if others == 0 then return v end
    return out
end
SL.hitbox.head_only = RB.keep_head

function Bind.clear_pub()
    if RB.hc ~= nil or RB.dmg ~= nil or RB.safe or RB.baim ~= nil or RB.head ~= nil or RB.strict or RB.pub_thp ~= nil then
        RB.hc, RB.dmg, RB.safe, RB.baim, RB.head, RB.strict, RB.pub_thp = nil, nil, false, nil, nil, false, nil
        VIS.dirty = true
    end
end

function RB.clear_target()
    RB.t_hp, RB.t_air, RB.t_move = nil, false, false
    RB.t_bd, RB.t_hd, RB.t_state, RB.t_trust = 0, 0, 1, 0
    if RB.t_addr ~= nil then RB.t_addr, RB.baim_until, RB.hs_until = nil, 0, 0 end
end

-- Headshot assist: is the head the right target for the picked candidate? Returns a reason
-- tag or nil. Needs resolver data for the target; every "do not trust" case returns nil.
function RB.head_reason(c)
    local rec = RES.by_pawn[RB.t_addr]
    if not rec or RES.unresolved(rec) then
        RB.t_trust = 0
        return nil
    end
    local trust = RES.trust(rec)
    RB.t_trust = trust
    if trust * 100 < CFG.hs_trust then return nil end
    if RB.t_air or STATE.lp_air then return nil end
    if not multi_on(CFG.hs_states, RB.t_state, ITEMS.HS_STATES) then return nil end
    local hd, bd, hp = c.hd, c.bd, c.hp
    if hd <= 0 then return nil end                               -- head not hittable from here
    if CFG.hs_body_first and bd >= hp then return nil end        -- one body shot already kills
    local need = CFG.hs_need
    if need == 1 then
        return (hd >= hp) and "LETHAL" or nil
    elseif need == 2 then
        if hd >= hp then return "LETHAL" end
        return (hd > bd * 1.25) and "DMG" or nil
    end
    return "TRUST"
end

function RB.eval_targets(lp)
    local grp = RB.wgroup
    RB.base_hc = Bind.base(SL.hc, grp)
    RB.base_dmg = Bind.base(SL.dmg, grp)

    local baim_ok = CFG.baim_on and (SL.baim.n + SL.hitbox.n) > 0
    local hs_ok = CFG.hs_on and CFG.enable and (SL.hitbox.n > 0 or (CFG.hs_gate and SL.dmg.n > 0))
    local need_trace = hs_ok or (baim_ok and (CFG.baim_lethal or CFG.baim_2x))
    local need_target = need_trace or (baim_ok and (CFG.baim_hp_on or CFG.baim_unres))
        or (CFG.dmg_cap and SL.dmg.n > 0)
        or ((CFG.hc_tgt_air ~= 0 or CFG.hc_tgt_move ~= 0 or CFG.unres_hc ~= 0) and SL.hc.n > 0)
    local eye, view = nil, nil
    if need_target then eye, view = safe(lp.eye_position, lp), safe(engine.view_angles) end
    if not eye or not view then
        RB.clear_target()
        RB.baim_reason, RB.hs_reason = nil, nil
        return
    end

    local aim_from = vector(eye.x, eye.y, eye.z - K.EYE_OFFSET)   -- compare against target origin
    local lim = CFG.baim_fov
    local players = safe(entity.players)
    local list, n = CAND.list, 0
    if type(players) == "table" then
        for i = 1, #players do
            local p = players[i]
            local pawn = type(p) == "table" and p.pawn or nil
            if pawn and safe(pawn.alive, pawn) == true and safe(pawn.is_enemy, pawn) == true then
                local o = safe(pawn.origin, pawn)
                if o then
                    local fov = U.fov(aim_from, o, view)
                    if fov <= lim then
                        n = n + 1
                        local c = list[n]
                        if not c then
                            c = {}
                            list[n] = c
                        end
                        c.pawn, c.fov, c.hp, c.bd, c.hd = pawn, fov, 100, 0, 0
                    end
                end
            end
        end
    end
    for i = n + 1, CAND.n do list[i].pawn = nil end
    CAND.n = n

    -- Partial selection sort: only the MAX_TARGETS closest are traced.
    local pick = nil
    for i = 1, min(n, K.MAX_TARGETS) do
        local m = i
        for j = i + 1, n do
            if list[j].fov < list[m].fov then m = j end
        end
        if m ~= i then list[i], list[m] = list[m], list[i] end
        local c = list[i]
        c.hp = safe(c.pawn.health, c.pawn) or 100
        if need_trace then
            local ids = RB.hitbox_ids(c.pawn)
            if ids then
                local need = c.hp + CFG.baim_margin
                for j = 1, #ids.body do
                    local d = RB.dmg_at(eye, c.pawn, ids.body[j])
                    if d > c.bd then c.bd = d end
                    if d >= need and not hs_ok then break end      -- the assist wants the real maximum
                end
                if ids.head and (hs_ok or (CFG.baim_2x and c.bd > 0 and c.bd * 2 >= need
                    and not (CFG.baim_lethal and c.bd >= need))) then
                    c.hd = RB.dmg_at(eye, c.pawn, ids.head)
                end
            end
        end
        if not pick then pick = c end
        if c.bd > 0 or c.hd > 0 or not need_trace then
            pick = c
            break
        end
    end

    local reason, hs = nil, nil
    if pick then
        local p = pick.pawn
        local addr = safe(p.address, p)
        if addr and addr ~= RB.t_addr then RB.t_addr, RB.baim_until, RB.hs_until = addr, 0, 0 end
        RB.t_hp, RB.t_bd, RB.t_hd = pick.hp, pick.bd, pick.hd
        RB.t_air = (safe(p.on_ground, p) == false)
        local pv = safe(p.velocity, p)
        local sp2 = pv and (pv.x * pv.x + pv.y * pv.y) or 0
        RB.t_move = sp2 > K.T_MOVE_SQR
        if band(safe(p.flags, p) or 0, K.FL_DUCKING) ~= 0 then RB.t_state = 2
        elseif sp2 < 25 then RB.t_state = 1
        elseif sp2 < K.T_WALK_SQR then RB.t_state = 3
        else RB.t_state = 4 end
        if baim_ok then
            local hp, bd = pick.hp, pick.bd
            local need = hp + CFG.baim_margin
            if CFG.baim_lethal and bd > 0 and bd >= need then
                reason = "LETHAL"
            elseif CFG.baim_2x and bd > 0 and bd * 2 >= need and pick.hd < hp then
                reason = "2X"
            elseif CFG.baim_hp_on and hp <= CFG.baim_hp then
                reason = "HP"
            end
        end
        if hs_ok and not reason then hs = RB.head_reason(pick) end
    else
        RB.clear_target()
    end

    if reason then
        RB.baim_reason, RB.baim_until = reason, RB.tick_n + K.HOLD_TICKS
    elseif RB.tick_n > RB.baim_until then
        RB.baim_reason = nil
    end
    if hs then
        RB.hs_reason, RB.hs_until = hs, RB.tick_n + K.HOLD_TICKS
    elseif reason or RB.tick_n > RB.hs_until then
        RB.hs_reason = nil
    end
end

function RB.decide(grp)
    local st = RB.state
    local airborne = (st == ST.AIR or st == ST.APEX)
    local strict, kbaim, kdmg, khead = bind_on(UI.k_strict), bind_on(UI.k_baim), bind_on(UI.k_dmg), bind_on(UI.k_head)
    if not CFG.baim_on then RB.baim_reason = nil end
    if not (CFG.hs_on and CFG.enable) then RB.hs_reason = nil end

    -- resolver synergy: how much do we trust the guess for the crosshair target?
    local trec = RB.t_addr and RES.by_pawn[RB.t_addr] or nil
    local unres = (trec ~= nil) and CFG.enable and RES.unresolved(trec) or false
    RB.t_unres = unres

    -- body or head? Keys first, then lethal body, then the headshot assist, then "unresolved".
    local baim, head = nil, nil
    if kbaim then
        baim = "KEY"
    elseif khead then
        head = "KEY"
    elseif RB.baim_reason then
        baim = RB.baim_reason
    elseif RB.hs_reason and not unres then
        head = RB.hs_reason
    elseif unres and CFG.baim_on and CFG.baim_unres then
        baim = unres
    end

    -- hitchance
    local hc = nil
    if airborne then
        if CFG.air_on then
            hc = (st == ST.APEX and CFG.apex_on) and CFG.apex_hc or CFG.air_hc
        end
    elseif CFG.hc_on then
        local v
        if st == ST.STAND then v = CFG.hc_stand
        elseif st == ST.SLOW then v = CFG.hc_slow
        elseif st == ST.MOVE then v = CFG.hc_move
        else v = CFG.hc_duck end
        if v and v > 0 then hc = v end
    end
    if hc and RB.t_hp then
        if RB.t_air then hc = hc + CFG.hc_tgt_air end
        if RB.t_move then hc = hc + CFG.hc_tgt_move end
    end
    -- bonuses (unresolved, head, strict) stack, but never past the overall cap; the cap never
    -- lowers the value the state / user already had
    local bonus = 0
    if unres and CFG.unres_hc ~= 0 then bonus = bonus + CFG.unres_hc end
    if head and CFG.hs_hc > 0 then bonus = bonus + CFG.hs_hc end
    if strict then bonus = bonus + CFG.strict_bonus end
    if bonus ~= 0 then
        if not hc then hc = RB.base_hc end
        if hc then hc = min(hc + bonus, max(CFG.hc_cap, hc)) end
    end
    if hc then hc = clamp(round(hc), 1, 100) end

    -- min damage
    local dmg = nil
    if airborne and CFG.air_on then dmg = CFG.air_dmg end
    if kdmg then dmg = CFG.dmg_bind_val end
    local gated = false
    if head and CFG.hs_gate and not kdmg and RB.t_hp and RB.t_bd > 0 and RB.t_hd > 0 then   -- needs a measured body damage
        -- just above the measured body damage, never above what the head deals or the target's HP
        local gate = min(floor(RB.t_bd) + 1, floor(RB.t_hd), RB.t_hp)
        if gate >= 1 and gate > (dmg or RB.base_dmg or 0) then dmg, gated = gate, true end
    end
    if CFG.dmg_cap and RB.t_hp then
        local base = dmg or RB.base_dmg
        if base and base <= 100 and RB.t_hp < base then dmg = max(1, RB.t_hp) end
    end
    if dmg then dmg = clamp(round(dmg), 1, 130) end

    -- safepoint, body-aim flag, hitbox list
    local want_safe_b = (airborne and CFG.air_on and CFG.air_safe) or strict
    local want_safe = want_safe_b and TRANSFORM or nil
    local want_baim = baim and TRANSFORM or nil
    Bind.apply(SL.hc, hc, grp)
    Bind.apply(SL.dmg, dmg, grp)
    Bind.apply(SL.safe, want_safe, grp)
    Bind.apply(SL.baim, want_baim, grp)
    Bind.apply(SL.hitbox, want_baim or (head and Bind.HEAD) or nil, grp)

    -- the panel shows only what is really written into the ragebot
    local hc_live, safe_live, dmg_live = SL.hc.live > 0, SL.safe.live > 0, SL.dmg.live > 0
    RB.set_pub("hc", hc_live and hc or nil)
    RB.set_pub("dmg", dmg_live and dmg or nil)
    RB.set_pub("safe", (want_safe_b and safe_live) and true or false)
    RB.set_pub("baim", (baim and SL.baim.live + SL.hitbox.live > 0) and baim or nil)
    RB.set_pub("head", (head and (SL.hitbox.live > 0 or (gated and dmg_live))) and head or nil)
    RB.set_pub("strict", (strict and (hc_live or safe_live)) and true or false)
    RB.set_pub("pub_thp", RB.t_hp)
end

-- ============================================================================
--  VISUALS
-- ============================================================================
VIS.font, VIS.ver = nil, "v" .. META.version .. " PP"
VIS.feed = {}
VIS.dirty, VIS.a, VIS.paused, VIS.focus_key, VIS.rebuilt_t = true, 0, nil, nil, 0
VIS.rows, VIS.nrows = {}, 0
VIS.size, VIS.w, VIS.h, VIS.pad, VIS.rh, VIS.th, VIS.tw = 0, 0, 0, 10, 18, 14, 14
VIS.memo, VIS.memo_n = {}, 0
VIS.drag, VIS.px, VIS.py, VIS.was_down = nil, nil, nil, false
VIS.panel_x, VIS.panel_y, VIS.panel_bottom = nil, nil, nil

VIS.IND_KEYS = { "MODE", "HC", "DMG", "SAFE", "BAIM", "STRICT", "TARGET", "AA", "YAW", "CONF", "PITCH", "HITS", "LC", "HEAD", "TRUST", "VIA" }
VIS.IND_VALS = { "PAUSE", "100%", "130", "ON", "LETHAL", "100 HP", "JITTER L*", "+180°", "FLICK", "99/99", "BREAK", "FREESTAND", "STANDING" }

function VIS.init()
    local ok, f = pcall(render.font, "segoeui.ttf", 13)
    if ok and f then
        local ok2, loaded = pcall(f.loaded, f)
        if ok2 and loaded then VIS.font = f end
    end
end

function VIS.text(x, y, col, str, size)
    if VIS.font then
        render.text(x, y, col, str, "", size, VIS.font)
    else
        render.text(x, y, col, str, "", size)
    end
end

function VIS.measure(str, size)
    local ok, w, h
    if VIS.font then
        ok, w, h = pcall(render.text_size, str, "", size, VIS.font)
    else
        ok, w, h = pcall(render.text_size, str, "", size)
    end
    if ok and type(w) == "number" then return w, (type(h) == "number") and h or size end
    return U.utf8_len(str) * size * 0.55, size
end

function VIS.text_w(str)
    local w = VIS.memo[str]
    if not w then
        if VIS.memo_n >= K.MEMO_MAX then VIS.memo, VIS.memo_n = {}, 0 end
        w = VIS.measure(str, VIS.size)
        VIS.memo[str] = w
        VIS.memo_n = VIS.memo_n + 1
    end
    return w
end

-- Event feed entry (hit / body / miss / kill / info).
function VIS.push(kind, text)
    local feed = VIS.feed
    feed[#feed + 1] = { kind = kind, text = text, t = globals.realtime() }
    if #feed > K.FEED_MAX then tremove(feed, 1) end
end

local function make_pal(r, g, b, qa)
    local k = qa / 255
    return {
        bg = color(10, 11, 17, floor(214 * k)), line = color(255, 255, 255, floor(24 * k)),
        acc = color(r, g, b, qa), acc_dim = color(r, g, b, floor(70 * k)),
        key = color(122, 126, 146, qa), val = color(236, 238, 246, qa),
        good = color(120, 220, 160, qa), warn = color(255, 190, 96, qa), bad = color(255, 110, 110, qa),
        _r = r, _g = g, _b = b, _qa = qa,
    }
end

-- Palettes are rebuilt only when the accent or the alpha changes.
function VIS.palette(slot, qa)
    local acc = CFG.accent
    local r, g, b = 140, 148, 255
    if type(acc) == "table" and type(acc.r) == "number" and type(acc.g) == "number" and type(acc.b) == "number" then
        r, g, b = acc.r, acc.g, acc.b
    end
    local p = VIS[slot]
    if p and p._r == r and p._g == g and p._b == b and p._qa == qa then return p end
    p = make_pal(r, g, b, qa)
    VIS[slot] = p
    return p
end

-- ---------------------------------------------------------------- overlay
function VIS.side_label(rec) return ((rec.pred_side > 0) and "L" or "R") .. (rec.manual and "*" or "") end

function VIS.live(rec, rt) return rec.pawn and rec.resolved and rt - rec.seen_rt < 0.2 end

-- Same font, same size and same text path (VIS.text / VIS.text_w) as the panel; the whole
-- label block is clamped to the screen.
function VIS.overlay(rt, P)
    local detailed = (CFG.ov_style == 2)
    local size = VIS.size
    local lh = size + 3
    local focus = RES.focus
    local sw = STATE.sw
    for _, rec in pairs(RES.records) do
        if VIS.live(rec, rt) then
            local ok, l, t, r = pcall(rec.pawn.bbox, rec.pawn)
            if ok and type(l) == "number" and type(t) == "number" and type(r) == "number" then
                local col = rec.lc and P.warn or (rec.applied and P.val or P.key)
                local dlt = normalize(rec.resolved_yaw - rec.raw_yaw)
                local txt = format("%s %s %d°%s", MODE_LABEL[rec.mode] or "?", VIS.side_label(rec), round(abs(dlt)), rec.lc and " LC" or "")
                local w = VIS.text_w(txt)
                local cx = (l + r) * 0.5
                local y = max(2, t - 6 - (detailed and 2 or 1) * lh)
                local x = clamp(cx - w * 0.5, 2, max(2, sw - w - 2))
                VIS.text(x, y, col, txt, size)
                if rec == focus then render.rect_filled(x, y + size + 1, w, 1, P.acc) end
                if detailed then
                    local sub = format("%d/%d · b%d%s%s", rec.hits, rec.misses, rec.brute_idx,
                        rec.pitch_kind ~= "" and (" · " .. rec.pitch_kind) or "",
                        rec.last_reason and (" · " .. rec.last_reason) or "")
                    local sw2 = VIS.text_w(sub)
                    VIS.text(clamp(cx - sw2 * 0.5, 2, max(2, sw - sw2 - 2)), y + lh, P.key, sub, size)
                    local bw = clamp(r - l, 24, 60)
                    local bx = clamp(cx - bw * 0.5, 2, max(2, sw - bw - 2))
                    render.rect_filled(bx, y + lh * 2, bw, 2, P.acc_dim)
                    render.rect_filled(bx, y + lh * 2, max(1, floor(bw * clamp(rec.conf, 0, 1))), 2, P.acc)
                end
            end
        end
    end
end

-- Short lines from the head: received yaw (dim) and resolved yaw (accent).
function VIS.yaw_lines(rt, P)
    for _, rec in pairs(RES.records) do
        if VIS.live(rec, rt) then
            local head = safe(rec.pawn.eye_position, rec.pawn) or rec.en_eye
            if head then
                local sx, sy = render.world_to_screen(head)
                if sx then
                    local a = rad(rec.raw_yaw)
                    local tx, ty = render.world_to_screen(vector(head.x + cos(a) * 18, head.y + sin(a) * 18, head.z))
                    if tx then render.line(sx, sy, tx, ty, P.key, 1) end
                    a = rad(rec.resolved_yaw)
                    tx, ty = render.world_to_screen(vector(head.x + cos(a) * 26, head.y + sin(a) * 26, head.z))
                    if tx then render.line(sx, sy, tx, ty, rec.applied and P.acc or P.acc_dim, 2) end
                    render.circle_filled(sx, sy, 2, P.acc, 10)
                end
            end
        end
    end
end

-- ---------------------------------------------------------------- status panel
function VIS.layout(size)
    VIS.size, VIS.memo, VIS.memo_n = size, {}, 0
    local kw, vw = 0, 0
    for i = 1, #VIS.IND_KEYS do kw = max(kw, VIS.text_w(VIS.IND_KEYS[i])) end
    for i = 1, #VIS.IND_VALS do vw = max(vw, VIS.text_w(VIS.IND_VALS[i])) end
    for i = 1, #ST_NAME do vw = max(vw, VIS.text_w(ST_NAME[i])) end
    local pad = floor(size * 0.8)
    local tw, th = VIS.measure("0x", size + 2)
    local vwid = VIS.measure(VIS.ver, size - 2)
    VIS.pad, VIS.rh, VIS.th, VIS.tw = pad, floor(size * 1.55), th, tw
    VIS.w = max(pad * 2 + kw + 18 + vw, pad * 2 + tw + 6 + vwid + 40, floor(size * 13))
end

function VIS.put_row(i, k, value, kind, frac)
    local r = VIS.rows[i]
    if not r then
        r = {}
        VIS.rows[i] = r
    end
    r[1], r[2], r[3], r[4], r[5] = k, value, kind, VIS.text_w(value), frac
    return i + 1
end

function VIS.rebuild(rb_show, rec)
    local put, n = VIS.put_row, 1
    if rb_show then
        n = put(n, "MODE", RB.paused and "PAUSE" or (RB.state and ST_NAME[RB.state] or "—"), 1)
        if RB.hc then n = put(n, "HC", RB.hc .. "%", 1) end
        if RB.dmg then n = put(n, "DMG", tostring(RB.dmg), 1) end
        if RB.safe then n = put(n, "SAFE", "ON", 2) end
        if RB.baim then n = put(n, "BAIM", RB.baim, 3) end
        if RB.head then n = put(n, "HEAD", RB.head, 2) end
        if RB.strict then n = put(n, "STRICT", "ON", 2) end
        if RB.pub_thp then n = put(n, "TARGET", RB.pub_thp .. " HP", 1) end
    end
    if rec then
        n = put(n, "AA", (MODE_LABEL[rec.mode] or "?") .. " " .. VIS.side_label(rec), rec.applied and 2 or 1)
        n = put(n, "YAW", format("%+d°", round(normalize(rec.resolved_yaw - rec.raw_yaw))), 1)
        n = put(n, "VIA", rec.mem_written and "MEM" or (CFG.cmd_fix and "CMD" or "OFF"), 1)
        if rec.pitch_kind ~= "" then n = put(n, "PITCH", rec.pitch_kind, 3) end
        if rec.lc then n = put(n, "LC", "BREAK", 3) end
        n = put(n, "CONF", format("%d%%", round(rec.conf * 100)), 4, rec.conf)
        n = put(n, "TRUST", format("%d%%", round(RES.trust(rec) * 100)), 1)
        n = put(n, "HITS", format("%d/%d", rec.hits, rec.misses), 1)
    end
    VIS.nrows = n - 1
    VIS.h = VIS.pad * 2 + VIS.th + 8 + VIS.nrows * VIS.rh + ((rb_show and RB.hc) and 8 or 0)
end

function VIS.commit_drag(w, h)
    local nx = clamp(round(VIS.px / max(1, STATE.sw - w) * 100), 0, 100)
    local ny = clamp(round(VIS.py / max(1, STATE.sh - h) * 100), 0, 100)
    if REG.panel_x then write_el(REG.panel_x, nx) end
    if REG.panel_y then write_el(REG.panel_y, ny) end
    CFG.panel_x, CFG.panel_y = nx, ny
    VIS.drag, VIS.px, VIS.py = nil, nil, nil
    SET.dirty, SET.dirty_t = true, STATE.rt
end

-- true when the cursor is over the Neverlose menu window (clicks there belong to the menu).
function VIS.over_menu(mx, my)
    local p, s = safe(ui.position), safe(ui.size)
    if type(p) ~= "table" or type(s) ~= "table" or type(p.x) ~= "number" or type(s.x) ~= "number" then return false end
    return mx >= p.x and mx <= p.x + s.x and my >= p.y and my <= p.y + s.y
end

-- Panel position; draggable with the left mouse button while the menu is open.
function VIS.position(w, h)
    local x = floor((STATE.sw - w) * CFG.panel_x / 100)
    local y = floor((STATE.sh - h) * CFG.panel_y / 100)
    if STATE.menu_open then
        local ok, mx, my = pcall(input.cursor)
        local down = safe(input.key_down, K.VK_LBUTTON) == true
        if ok and type(mx) == "number" and type(my) == "number" then
            if VIS.drag then
                if down then
                    VIS.px = clamp(mx - VIS.drag.dx, 0, max(0, STATE.sw - w))
                    VIS.py = clamp(my - VIS.drag.dy, 0, max(0, STATE.sh - h))
                else
                    VIS.commit_drag(w, h)
                end
            elseif down and not VIS.was_down and mx >= x and mx <= x + w and my >= y and my <= y + h
                and not VIS.over_menu(mx, my) then
                VIS.drag = { dx = mx - x, dy = my - y }
                VIS.px, VIS.py = x, y
            end
        end
        VIS.was_down = down
    else
        if VIS.drag then VIS.commit_drag(w, h) end
        VIS.was_down = false
    end
    if VIS.px then return VIS.px, VIS.py end
    return x, y
end

function VIS.panel(rt)
    local rb_show = CFG.rb_enable and (RB.state ~= nil or RB.paused)
    local rec = CFG.enable and RES.focus or nil
    if rec and (not rec.resolved or rt - rec.seen_rt > 0.5) then rec = nil end
    local show = (rb_show or rec ~= nil) and RB.in_game
    local a = VIS.a
    if not show and a == 0 then return end
    a = a + ((show and 1 or 0) - a) * min(1, (safe(globals.frametime) or 0.016) * 10)
    if a < 0.02 then
        VIS.a = show and a or 0
        return
    end
    VIS.a = a
    if STATE.sw <= 0 or STATE.sh <= 0 then return end

    local size = round(13 * CFG.panel_scale / 100)
    if size ~= VIS.size then
        VIS.layout(size)
        VIS.dirty = true
    end
    local rkey = rec and rec.key or nil
    if VIS.dirty or RB.paused ~= VIS.paused or rkey ~= VIS.focus_key or (rec and rt - VIS.rebuilt_t > 0.1) then
        VIS.rebuild(rb_show, rec)
        VIS.paused, VIS.focus_key, VIS.dirty, VIS.rebuilt_t = RB.paused, rkey, false, rt
    end

    local P = VIS.palette("pal_panel", round(a * 255))
    local w, h, pad = VIS.w, VIS.h, VIS.pad
    local x, y = VIS.position(w, h)

    render.rect_filled(x, y, w, h, P.bg, 7)
    render.rect(x, y, w, h, P.line, 7, 1)
    render.rect_filled(x + 1, y + 10, 2, max(1, h - 20), P.acc, 1)
    VIS.text(x + pad, y + pad - 1, P.acc, "0x", size + 2)
    VIS.text(x + pad + VIS.tw + 6, y + pad + 1, P.key, VIS.ver, size - 2)
    local ry = y + pad + VIS.th + 8
    render.line(x + pad, ry - 4, x + w - pad, ry - 4, P.line, 1)
    for i = 1, VIS.nrows do
        local row = VIS.rows[i]
        local col = P.val
        if row[3] == 2 then col = P.good elseif row[3] == 3 then col = P.warn end
        VIS.text(x + pad, ry, P.key, row[1], size)
        if row[3] == 4 then
            local bw = floor(w * 0.32)
            local bx = x + w - pad - row[4] - 6 - bw
            local by = ry + floor(size * 0.5)
            render.rect_filled(bx, by, bw, 3, P.acc_dim, 1)
            render.rect_filled(bx, by, max(2, floor(bw * clamp(row[5] or 0, 0, 1))), 3, P.acc, 1)
        end
        VIS.text(x + w - pad - row[4], ry, col, row[2], size)
        ry = ry + VIS.rh
    end
    if rb_show and RB.hc then
        local bw = w - pad * 2
        render.rect_filled(x + pad, y + h - 9, bw, 3, P.acc_dim, 1)
        render.rect_filled(x + pad, y + h - 9, max(2, floor(bw * RB.hc / 100)), 3, P.acc, 1)
    end
    VIS.panel_x, VIS.panel_y, VIS.panel_bottom = x, y, y + h
end

-- ---------------------------------------------------------------- event feed
function VIS.feed_draw(rt, P)
    local feed = VIS.feed
    while #feed > 0 and rt - feed[1].t > K.FEED_LIFE do tremove(feed, 1) end
    if #feed == 0 then return end
    local size = round(12 * CFG.panel_scale / 100)
    local x, y
    if VIS.a > 0.02 and VIS.panel_x then
        x, y = VIS.panel_x, VIS.panel_bottom + 8
    else
        x = floor((STATE.sw - 200) * CFG.panel_x / 100)
        y = floor((STATE.sh - 100) * CFG.panel_y / 100)
    end
    for i = 1, #feed do
        local e = feed[i]
        local a = clamp(K.FEED_LIFE - (rt - e.t), 0, 1)
        local col = P.val
        if e.kind == "hit" then col = P.good
        elseif e.kind == "miss" then col = P.warn
        elseif e.kind == "kill" then col = P.acc
        elseif e.kind == "info" then col = P.key end
        VIS.text(x + 2, y, (a < 1) and col:alpha(floor(col.a * a)) or col, e.text, size)
        y = y + size + 4
    end
end


-- ---------------------------------------------------------------- stats label (1 Hz)
function VIS.stats(rt)
    if rt - STATE.last_label < 1 then return end
    STATE.last_label = rt
    local tracked = 0
    for _, rec in pairs(RES.records) do
        if rt - rec.seen_rt < 1 then tracked = tracked + 1 end
    end
    local s = RES.stats
    local flips = {}
    for k, v in pairs(RES.flipped) do
        if v then flips[#flips + 1] = k end
    end
    tsort(flips)
    if UI.stats and not is_dummy(UI.stats) then
        pcall(UI.stats.set, UI.stats, format("tracked %d · hits %d (%d hs) · misses %d (hard %d · soft %d · resolver %d) · aim_ack %s · yaw via %s%s",
            tracked, s.hits or 0, s.heads or 0, s.misses or 0, s.hard or 0, s.soft or 0, s.resolver or 0,
            RES.ack_live and RES.ack_live() and "live" or RES.ack_mode,
            RES.can_write() and "memory" or (CFG.cmd_fix and "cmd" or "off"),
            #flips > 0 and (" · flipped: " .. tconcat(flips, ",")) or ""))
    end
end

function VIS.paint()
    local rt = STATE.rt
    VIS.stats(rt)
    if not CFG.enable and not CFG.rb_enable then
        VIS.a = 0
        return
    end
    local size = round(13 * CFG.panel_scale / 100)
    if size ~= VIS.size then
        VIS.layout(size)
        VIS.dirty = true
    end
    local P = VIS.palette("pal_full", 255)
    if CFG.enable and RB.in_game then
        if CFG.overlay then VIS.overlay(rt, P) end
        if CFG.yaw_lines then VIS.yaw_lines(rt, P) end
    end
    if CFG.panel then VIS.panel(rt) else VIS.a = 0 end
    if CFG.feed and RB.in_game then VIS.feed_draw(rt, P) end
end

-- ============================================================================
--  LIFECYCLE
--  Every handler runs through run(): errors are caught per handler and counted per MODULE
--  (core / res / rage / vis). A module that keeps failing is suspended, then stopped, on its
--  own: a visuals bug can no longer take the resolver or the rage assist down with it.
--    createmove : angles -> resolver cmd correction -> local state -> rage assist
--    frame_stage: resolver (net update end) / re-apply (lag compensation)
--    paint      : background tasks (core) -> visuals (vis)
-- ============================================================================
local EVENTS = {}

local TRIP = {
    rage = function()
        pcall(Bind.release, true)
        pcall(RB.reset)
        pcall(Journal.flush, true)
        RB.paused = false
    end,
    res  = function() RES.focus, RES.pending = nil, {} end,
    vis  = function() VIS.a, VIS.drag = 0, nil end,
    core = function() end,
}

local function trip(mod, name)
    local m = MODS[mod]
    m.strikes, m.strike_t = m.strikes + 1, STATE.rt
    pcall(TRIP[mod])
    if m.strikes >= K.ERR_STRIKES then
        m.dead = true
        notify(format("Module '%s' stopped after repeated errors in '%s'. The other modules keep running; fix the cause and Save & Reload.", mod, name))
    else
        m.hold = STATE.rt + K.ERR_COOLDOWN
        notify(format("Errors in '%s': module '%s' suspended for %d s.", name, mod, K.ERR_COOLDOWN))
    end
end

local function run(mod, name, fn, a, b, c)
    local m = MODS[mod]
    if m.dead then return false end
    local rt = globals.realtime()
    STATE.rt = rt
    if m.hold then
        if rt < m.hold then return false end
        m.hold = nil
    end
    local ok, err = pcall(fn, a, b, c)
    if ok then
        if m.errs[name] then m.errs[name] = 0 end
        return true
    end
    report(name, err)
    local n = (m.errs[name] or 0) + 1
    m.errs[name] = n
    if n >= K.ERR_LIMIT then
        m.errs[name] = 0
        trip(mod, name)
    end
    return false
end

-- Game event / engine event by name (events.on).
local function on(event, mod, name, fn)
    local ok, id = pcall(events.on, event, function(a, b, c) run(mod, name, fn, a, b, c) end)
    if ok and id ~= nil then
        EVENTS[#EVENTS + 1] = function() pcall(events.off, id) end
        return true
    end
    say("event '" .. event .. "' not available: " .. tostring(id))
    return false
end

local LIFE = {}

-- Createmove: the resolver gets the command first (it may correct the aim), then the local
-- movement state is refreshed and the rage assist decides.
function LIFE.createmove(cmd)
    STATE.rt = globals.realtime()
    local lp = entity.local_pawn()
    if lp and safe(lp.alive, lp) ~= true then lp = nil end
    STATE.lp_dead = (lp == nil)

    local a = safe(cmd.view_angles, cmd)
    if a then STATE.raw_p, STATE.raw_y = a.x, a.y else STATE.raw_p, STATE.raw_y = nil, nil end
    if lp then run("res", "cmd_fix", RES.cmd_fix, cmd, lp) end
    a = safe(cmd.view_angles, cmd)
    if a then STATE.cmd_p, STATE.cmd_y = a.x, a.y else STATE.cmd_p, STATE.cmd_y = nil, nil end

    if lp then
        run("core", "movement", RB.movement, lp, cmd)
        run("res", "spread", RES.sample_spread, lp)
    else
        STATE.lp_air, STATE.lp_moving, RB.mstate = false, false, nil
    end
    if STATE.rt - RB.paint_t > K.PAINT_TIMEOUT then run("core", "background", RB.background, STATE.rt) end
    run("rage", "tick", RB.tick, cmd, lp)
end

function LIFE.core_paint()
    local now = STATE.rt
    RB.paint_t = now
    RB.background(now)
    -- createmove went silent (left the server, stalled simulation): never keep our overrides.
    if now - RB.cm_t > K.CM_TIMEOUT and (RB.touched or RB.state ~= nil or RB.paused) then
        RB.paused = false
        Bind.release(false)
        RB.reset()
    end
end

function LIFE.paint()
    STATE.rt = globals.realtime()
    run("core", "background", LIFE.core_paint)
    run("vis", "paint", VIS.paint)
end

function LIFE.unload()
    STATE.rt = globals.realtime()
    pcall(RB.on_unload)
    pcall(RES.store_save, false)
    if SET.dirty then pcall(IO.save) end
    for i = 1, #EVENTS do pcall(EVENTS[i]) end
    say("unloaded")
end

function LIFE.boot()
    STATE.rt = globals.realtime()
    local ok_dt, dt = pcall(globals.interval)
    if ok_dt and type(dt) == "number" and dt > 0 then RB.g_tick = K.GRAVITY * dt end
    local sw, sh = render.screen_size()
    if type(sw) == "number" and type(sh) == "number" then STATE.sw, STATE.sh = sw, sh end

    VIS.init()
    build_menu()
    IO.load()                                    -- snapshot first: it may carry manual paths
    local migrated = SET.dirty
    refresh_all()
    PS.last = CFG.preset
    on_settings_changed(nil)                     -- drift check only
    SET.dirty = migrated

    local restored = Journal.restore()
    local scanned = Bind.scan()
    RB.boot_status = scanned and Bind.summary() or "config.keys unavailable"
    RB.set_status(RB.boot_status)

    RES.store_load()
    RES.insecure = safe(client.insecure) == true
    STATE.insecure = RES.insecure
    local ok, open = pcall(input.menu_open)
    STATE.menu_open = ok and open == true

    on("frame_stage",    "res",  "frame",       RES.frame)
    on("createmove",     "core", "createmove",  LIFE.createmove)
    on("weapon_fire",    "res",  "weapon_fire", RES.on_weapon_fire)
    on("player_hurt",    "res",  "player_hurt", RES.on_player_hurt)
    on("player_death",   "res",  "player_death", RES.on_player_death)
    on("round_start",    "res",  "round_start", RES.on_round_start)
    on("menu_toggled",   "core", "menu",        RB.on_menu_toggled)
    on("level_init",     "core", "level_init",  function()
        local ok, err = pcall(RES.on_level_init)
        if not ok then report("resolver level_init", err) end
        RB.on_level()
    end)
    on("level_shutdown", "core", "level_shutdown", function()
        local ok, err = pcall(RES.on_level_shutdown)
        if not ok then report("resolver level_shutdown", err) end
        RB.on_level()
    end)
    local pok, pid = pcall(events.on, "paint", LIFE.paint)
    if pok and pid ~= nil then
        EVENTS[#EVENTS + 1] = function() pcall(events.off, pid) end
    else
        say("event 'paint' not available: " .. tostring(pid))
    end
    local uok, uerr = pcall(events.on, "unload", LIFE.unload)
    if not uok then say("unload hook failed: " .. tostring(uerr)) end

    RES.ack_mode = on_cheat("aim_ack", "res", "aim_ack", RES.on_aim_ack) or "unavailable"

    if restored > 0 then notify("Restored " .. restored .. " ragebot values after a crash") end
    say(format("v%s %s loaded · insecure=%s · resolver module=%s · aim_ack=%s · paths: %s", META.version, META.edition,
        tostring(STATE.insecure), RES.stub and "MISSING" or "ok", RES.ack_mode, RB.boot_status))
    if scanned and Bind.total() == 0 then
        notify("No ragebot paths found in config. Use 'Dump paths to console' on the 0x Rage tab.")
    else
        notify(format("%s v%s %s loaded · %s", META.name, META.version, META.edition, META.credits))
    end
end

local boot_ok, boot_err = pcall(LIFE.boot)
if not boot_ok then
    for _, m in pairs(MODS) do m.dead = true end
    pcall(Bind.release, true)
    pcall(Journal.flush, true)
    say("boot error: " .. tostring(boot_err))
end
