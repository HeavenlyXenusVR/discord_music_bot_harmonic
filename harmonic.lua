--[[
  Harmonic -- GWS Music Bot (Harmonic), node `harmonic` of the 13-bot swarm.
  LuaJIT port of harmonic.py. Full command-surface parity target; see the
  "Known simplifications" note near the bottom of this file for the handful
  of Python-only subsystems (local yt-dlp audio caching, BPM/loudness
  analysis via aubio, YouTube Data API playlist expansion, distributed
  claim-token recovery) that don't have a LuaJIT/Lavalink equivalent and
  were intentionally left out rather than half-ported.

  Flavor: Harmonic is the "chill, blended listening sessions" node -- smooth
  volume-ramp fades (not hard cuts), a Smart Auto-DJ that learns per-user and
  per-server taste, personal playlists, and a taste/leaderboard/history layer
  for a social listening feel. Keep responses warm and a little musical.
]]

package.path = "./lib/?.lua;./lib/?/init.lua;" .. package.path

local copas = require("copas")
local cjson = require("cjson")
local https = require("ssl.https")
local ltn12 = require("ltn12")

local Bot = require("swarmlua.bot")

-- This LuaJIT build doesn't expose table.unpack (5.2+ name) globally unless
-- LUAJIT_ENABLE_LUA52COMPAT was set at compile time; fall back to the 5.1
-- global `unpack`. Same fix already applied centrally in lib/swarmlua/pg.lua;
-- needed here too for the IN (...) parameter spreads below.
local unpack = table.unpack or unpack

math.randomseed(os.time() + (tonumber(tostring({}):match("0x(%x+)"), 16) or 0))

-- ============================================================================
-- Config
-- ============================================================================

local BOT_NAME = "harmonic"
local PREFIX = "harmonic_main_"

local function env(name, default)
  local v = os.getenv(name)
  if v == nil or v == "" then return default end
  return v
end

local TOKEN = env("HARMONIC_DISCORD_TOKEN", "")
if TOKEN == "" then
  io.stderr:write("[harmonic] HARMONIC_DISCORD_TOKEN is not set; refusing to start.\n")
  os.exit(1)
end

local DB_CONFIG = {
  host = env("HARMONIC_DB_HOST", env("DB_HOST", "127.0.0.1")),
  port = tonumber(env("HARMONIC_DB_PORT", env("DB_PORT", "5432"))),
  user = env("HARMONIC_DB_USER", env("DB_USER", "botuser")),
  password = env("HARMONIC_DB_PASSWORD", env("DB_PASSWORD", "bot_logins")),
  database = env("HARMONIC_DB_NAME", "discord_music_harmonic"),
}

local function parse_lavalink_uri(uri)
  uri = uri or "http://127.0.0.1:2333"
  local host, port = uri:match("^https?://([^:/]+):?(%d*)/?$")
  if not host then host = "127.0.0.1" end
  if not port or port == "" then port = "2333" end
  return host, tonumber(port)
end

local LAVALINK_URI = env("HARMONIC_LAVALINK_URI", env("LAVALINK_URI", "http://127.0.0.1:2333"))
local LAVALINK_PASSWORD = env("HARMONIC_LAVALINK_PASSWORD", env("LAVALINK_PASSWORD", ""))
local ll_host, ll_port = parse_lavalink_uri(LAVALINK_URI)

local ERROR_WEBHOOK_URL = env("HARMONIC_ERROR_WEBHOOK_URL", env("SWARM_ERROR_WEBHOOK_URL", ""))

-- Minimal, bot-specific intents: GUILDS(1) + GUILD_VOICE_STATES(128).
-- Harmonic only needs slash-command interactions and voice-state tracking;
-- it does not read message content or need the privileged members intent.
local INTENTS = 1 + 128

local bot = Bot.new({
  token = TOKEN,
  intents = INTENTS,
  db = DB_CONFIG,
  lavalink = { host = ll_host, port = ll_port, password = LAVALINK_PASSWORD },
})

bot.start_time = os.time()

-- ============================================================================
-- In-memory runtime state (mirrors the Python file's module-level dicts)
-- ============================================================================

local playback_tracking = {}   -- guild_id -> {start_time, offset, url, title, duration, ...}
local guild_states = {}        -- guild_id -> {voice_channel_id, position, track_uid, url, title}
local processing_guild = {}    -- guild_id -> true while process_queue is running (poor-man's lock)
local voice_states = {}        -- guild_id -> { [user_id] = {channel_id=, is_bot=} }
local sleep_timers = {}        -- guild_id -> wake monotonic time (0 = cancelled)
local vote_skip_sessions = {}  -- guild_id -> { [user_id]=true }
local queue_votes = {}         -- "guild:queue_id" -> {up={}, down={}}
local prefetch_cache = {}      -- guild_id -> {url=, track=, expires_at=}
local member_name_cache = {}   -- user_id -> {name=, expires_at=}
local feedback_dedupe = {}     -- key -> monotonic expiry
local autodj_fail_until = {}   -- guild_id -> monotonic time to avoid retrying autodj

local TRACK_FEEDBACK_BROADCAST = env("HARMONIC_TRACK_FEEDBACK_BROADCAST", "true") ~= "false"

-- ============================================================================
-- Small helpers
-- ============================================================================

local function now() return os.time() end
local function mono() return copas.gettime and copas.gettime() or os.clock() end

local function trim(s) return (tostring(s or ""):gsub("^%s+", ""):gsub("%s+$", "")) end

local function random_hex(len)
  local chars = "0123456789abcdef"
  local out = {}
  for i = 1, len do
    local idx = math.random(1, 16)
    out[i] = chars:sub(idx, idx)
  end
  return table.concat(out)
end

local function new_track_uid() return random_hex(32) end

local function clamp(v, lo, hi) return math.max(lo, math.min(hi, v)) end

local function compact_title(title, limit)
  limit = limit or 72
  title = tostring(title or "")
  if #title > limit then return title:sub(1, limit - 1) .. "…" end
  return title
end

local function track_uid_label(uid)
  if not uid then return "unknown" end
  return tostring(uid):sub(1, 8)
end

-- Simple URL-key for intelligence/affinity/cooccurrence tables (mirrors _track_key:
-- prefer the URL, normalized; fall back to a lowercased title hash).
local function track_key(video_url, title)
  local basis = trim(video_url) ~= "" and trim(video_url) or trim(title)
  basis = basis:lower()
  -- cheap stable hash -> hex, capped at 64 chars (column width)
  local hash = 5381
  for i = 1, #basis do
    hash = (hash * 33 + basis:byte(i)) % 4294967296
  end
  return (basis:gsub("[^%w]", "_"):sub(1, 40)) .. "_" .. string.format("%x", hash)
end

local function is_explicit_lavalink_query(value)
  value = tostring(value or "")
  return value:match("^https?://") ~= nil
    or value:match("^%a+search:") ~= nil
    or value:match("^ytsearch:") ~= nil
end

-- ============================================================================
-- Embed / interaction response helpers (bot.lua only wires up a plain
-- immediate reply; Harmonic needs defer/followup/edit for slash commands
-- that hit the database or Lavalink before responding).
-- ============================================================================

local COLOR = {
  green = 0x2ECC71, red = 0xE74C3C, blue = 0x3498DB, blurple = 0x5865F2,
  gold = 0xF1C40F, orange = 0xE67E22, purple = 0x9B59B6, dark_purple = 0x71368A,
  grey = 0x2B2D31,
}

local function embed(opts)
  local e = { color = opts.color or COLOR.blurple }
  if opts.title then e.title = opts.title end
  if opts.description then e.description = opts.description end
  if opts.footer then e.footer = { text = opts.footer } end
  if opts.author then e.author = { name = opts.author } end
  if opts.fields then e.fields = opts.fields end
  return e
end

local function field(name, value, inline)
  return { name = name, value = tostring(value), inline = inline ~= false }
end

local function interaction_ack(interaction, itype, data)
  return bot.rest:post(("/interactions/%s/%s/callback"):format(interaction.id, interaction.token), {
    type = itype, data = data,
  })
end

-- type 4: immediate channel message response
local function reply(interaction, e, ephemeral)
  return interaction_ack(interaction, 4, { embeds = { e }, flags = ephemeral and 64 or nil })
end

local function reply_text(interaction, text, ephemeral)
  return interaction_ack(interaction, 4, { content = text, flags = ephemeral and 64 or nil })
end

-- type 5: deferred response ("thinking...")
local function defer(interaction, ephemeral)
  return interaction_ack(interaction, 5, ephemeral and { flags = 64 } or nil)
end

-- type 6: deferred component ack (no visible "thinking")
local function defer_update(interaction)
  return interaction_ack(interaction, 6, nil)
end

-- type 7: update the original message in place (component interactions)
local function update_message(interaction, e, view)
  return interaction_ack(interaction, 7, { embeds = { e }, components = view })
end

local function followup(interaction, e, ephemeral)
  return bot.rest:post(("/webhooks/%s/%s"):format(bot.application_id, interaction.token), {
    embeds = { e }, flags = ephemeral and 64 or nil,
  })
end

local function followup_text(interaction, text, ephemeral)
  return bot.rest:post(("/webhooks/%s/%s"):format(bot.application_id, interaction.token), {
    content = text, flags = ephemeral and 64 or nil,
  })
end

-- type 8: autocomplete response
local function autocomplete_reply(interaction, choices)
  return interaction_ack(interaction, 8, { choices = choices })
end

local function opt_value(interaction, name, default)
  local opts = interaction.data and interaction.data.options
  if not opts then return default end
  for _, o in ipairs(opts) do
    if o.name == name then return o.value end
  end
  return default
end

local function resolved_user(interaction, user_id)
  local resolved = interaction.data and interaction.data.resolved
  if not resolved then return nil end
  local member = resolved.members and resolved.members[tostring(user_id)]
  local user = resolved.users and resolved.users[tostring(user_id)]
  local name = (member and member.nick) or (user and user.global_name) or (user and user.username) or ("user " .. tostring(user_id))
  return { id = user_id, display_name = name, is_bot = user and user.bot }
end

-- ============================================================================
-- Permissions / DJ check
-- ============================================================================

local ADMINISTRATOR = 0x8

local guild_owner_cache = {} -- guild_id -> owner user_id

local function get_guild_owner_id(guild_id)
  if not guild_id then return nil end
  local cached = guild_owner_cache[guild_id]
  if cached then return cached end
  local g = bot.rest:get("/guilds/" .. tostring(guild_id))
  local owner_id = g and g.owner_id
  if owner_id then guild_owner_cache[guild_id] = owner_id end
  return owner_id
end

local function member_is_admin(interaction)
  local perms = interaction.member and interaction.member.permissions
  local n = perms and tonumber(perms)
  if n and math.floor(n / ADMINISTRATOR) % 2 == 1 then return true end
  -- The guild owner always effectively has admin, but Discord's resolved
  -- member.permissions bitfield on the interaction has been observed to not
  -- reliably reflect that -- fall back to an explicit ownership check
  -- rather than ever locking the actual owner out of admin-gated commands.
  local uid = interaction.member and interaction.member.user and interaction.member.user.id
  local owner_id = uid and get_guild_owner_id(interaction.guild_id)
  return owner_id ~= nil and tostring(owner_id) == tostring(uid)
end

local function member_has_role(interaction, role_id)
  if not role_id then return false end
  local roles = interaction.member and interaction.member.roles
  if not roles then return false end
  for _, r in ipairs(roles) do
    if tostring(r) == tostring(role_id) then return true end
  end
  return false
end

-- ============================================================================
-- Database helpers
-- ============================================================================

local db = bot.db

local function q(sql, ...)
  local rows, err = db:query(sql, ...)
  if not rows then
    print(("[harmonic] db error: %s | sql=%s"):format(tostring(err), sql:sub(1, 200)))
  end
  return rows, err
end

local function q1(sql, ...)
  local rows = q(sql, ...)
  return rows and rows[1] or nil
end

-- ============================================================================
-- Error events: mirrors harmonic.py's _persist_error_event()/send_error_webhook_log()
-- -- writes into the shared harmonic_error_events table (same table Aria/SwarmPanel
-- read from for the cross-bot error dashboard) and, if configured, posts to a
-- dedicated error webhook. Ported the same way gws.lua added this (see that
-- bot's final report): command/button handler failures are wired in via
-- bot.on_error (an additive, optional hook -- see lib/swarmlua/bot.lua), and
-- process_queue/heartbeat/direct-order-poll loops call report_error directly.
-- ============================================================================

local function shorten(s, limit)
  s = tostring(s or "")
  if #s <= limit then return s end
  return s:sub(1, limit - 3) .. "..."
end

local function persist_error_event(guild_id, level, error_type, title, description)
  q([[INSERT INTO harmonic_error_events (bot_name, guild_id, error_level, error_type, title, description)
      VALUES ('harmonic', %s, %s, %s, %s, %s)]],
    guild_id, level, error_type, shorten(title, 255), shorten(description, 5000))
end

local function send_error_webhook(title, description)
  if ERROR_WEBHOOK_URL == "" then return end
  local body = cjson.encode({ embeds = { {
    title = "🔴 Harmonic Error: " .. shorten(title, 200),
    description = shorten(description, 4000),
    color = 0xE74C3C,
    footer = { text = "Harmonic Music Bot" },
  } } })
  local resp = {}
  https.request({
    url = ERROR_WEBHOOK_URL, method = "POST",
    headers = { ["Content-Type"] = "application/json", ["Content-Length"] = tostring(#body) },
    source = ltn12.source.string(body), sink = ltn12.sink.table(resp),
  })
end

-- guild_id may be nil (process-wide failures, e.g. the heartbeat loop).
local function report_error(guild_id, error_type, title, description)
  local ok, err = pcall(persist_error_event, guild_id, "error", error_type, title, description)
  if not ok then print("[harmonic] failed to persist error event: " .. tostring(err)) end
  local ok2, err2 = pcall(send_error_webhook, title, description)
  if not ok2 then print("[harmonic] failed to send error webhook: " .. tostring(err2)) end
end

-- Wired into swarmlua.bot's additive/optional on_error hook (see
-- lib/swarmlua/bot.lua) so command and button handler failures also land in
-- harmonic_error_events / the error webhook, not just process_queue/heartbeat/
-- direct-order-poll below.
bot.on_error = function(name, interaction, err)
  report_error(interaction and interaction.guild_id, "command_error", tostring(name), tostring(err))
end

local function ensure_guild_settings(guild_id)
  q("INSERT INTO harmonic_guild_settings (guild_id) VALUES (%s) ON CONFLICT (guild_id) DO NOTHING", guild_id)
end

local function get_guild_settings(guild_id)
  ensure_guild_settings(guild_id)
  local row = q1("SELECT * FROM harmonic_guild_settings WHERE guild_id = %s", guild_id)
  return row or {}
end

local function set_guild_setting(guild_id, column, value)
  ensure_guild_settings(guild_id)
  -- column is always a hardcoded literal at call sites -- never user input.
  q(("UPDATE harmonic_guild_settings SET %s = %%s WHERE guild_id = %%s"):format(column), value, guild_id)
end

local function get_home_channel_id(guild_id)
  local row = q1("SELECT home_vc_id FROM harmonic_bot_home_channels WHERE guild_id = %s AND bot_name = 'harmonic'", guild_id)
  return row and row.home_vc_id
end

local function is_dj(interaction, silent)
  if member_is_admin(interaction) then return true end
  local settings = get_guild_settings(interaction.guild_id)
  if settings.dj_only_mode then
    if settings.dj_role_id and member_has_role(interaction, settings.dj_role_id) then return true end
    if not silent then
      reply(interaction, embed({ description = "❌ **Strict DJ Mode is Active.** You need the DJ Role.", color = COLOR.red }), true)
    end
    return false
  end
  return true
end

-- ============================================================================
-- Voice-state cache (Harmonic-local; the shared gateway only tracks the
-- bot's own voice session for Lavalink handoff, not other members).
-- ============================================================================

bot.gateway:on("VOICE_STATE_UPDATE", function(d)
  voice_states[d.guild_id] = voice_states[d.guild_id] or {}
  if d.channel_id and d.channel_id ~= cjson.null then
    voice_states[d.guild_id][d.user_id] = {
      channel_id = d.channel_id,
      is_bot = d.member and d.member.user and d.member.user.bot or (d.user_id == bot.user_id),
    }
  else
    voice_states[d.guild_id][d.user_id] = nil
  end
end)

local function channel_human_listeners(guild_id, channel_id)
  local out = {}
  local gv = voice_states[guild_id]
  if not gv then return out end
  for uid, v in pairs(gv) do
    if v.channel_id == channel_id and not v.is_bot then table.insert(out, uid) end
  end
  return out
end

local function channel_member_ids(guild_id, channel_id)
  local out = {}
  local gv = voice_states[guild_id]
  if not gv then return out end
  for uid, v in pairs(gv) do
    if v.channel_id == channel_id then table.insert(out, uid) end
  end
  return out
end

-- ============================================================================
-- Member display-name resolution (REST, cached)
-- ============================================================================

local function resolve_requester_name(guild_id, user_id)
  if not user_id then return "Auto-DJ" end
  if tostring(user_id) == tostring(bot.user_id) then return "Auto-DJ" end
  local cached = member_name_cache[tostring(user_id)]
  if cached and cached.expires_at > now() then return cached.name end
  local name = "user " .. tostring(user_id)
  local member = bot.rest:get(("/guilds/%s/members/%s"):format(guild_id, user_id))
  if member then
    name = member.nick or (member.user and (member.user.global_name or member.user.username)) or name
  end
  member_name_cache[tostring(user_id)] = { name = name, expires_at = now() + 300 }
  return name
end

-- ============================================================================
-- Track intelligence / affinity / cooccurrence (Smart Auto-DJ learning layer)
-- ============================================================================

-- harmonic_track_intelligence's and harmonic_user_track_affinity's counter
-- columns (queued_count, play_count, finish_count, skip_count, like_count,
-- dislike_count, total_listen_seconds for the former; the same minus
-- total_listen_seconds for the latter) are all NOT NULL with no column
-- default in Postgres (unlike the MySQL schema the Python original assumed,
-- which coerced a missing column to 0) -- every INSERT must zero-fill all of
-- them explicitly or the insert half of the ON CONFLICT upsert fails with a
-- not-null violation. Found via db_smoke_test.lua against the real database;
-- fixed the same way gws.lua's bump_track_intelligence_* functions already
-- handle it (see that bot's report).
local TI_COUNTERS = { "queued_count", "play_count", "finish_count", "skip_count", "like_count", "dislike_count" }

local function bump_track_intelligence(guild_id, video_url, title, requester_id, field_name)
  local key = track_key(video_url, title)
  local zero_fill = {}
  for _, c in ipairs(TI_COUNTERS) do zero_fill[#zero_fill + 1] = (c == field_name) and 1 or 0 end
  q(([[
    INSERT INTO harmonic_track_intelligence (guild_id, url_key, video_url, title, queued_count, play_count, finish_count, skip_count, like_count, dislike_count, total_listen_seconds, last_requester_id, source, first_seen, last_queued, updated_at)
    VALUES (%%s, %%s, %%s, %%s, %d, %d, %d, %d, %d, %d, 0, %%s, 'lavalink', NOW(), NOW(), NOW())
    ON CONFLICT (guild_id, url_key) DO UPDATE SET
      %s = harmonic_track_intelligence.%s + 1,
      video_url = EXCLUDED.video_url, title = EXCLUDED.title,
      last_requester_id = EXCLUDED.last_requester_id, last_queued = NOW(), updated_at = NOW()
  ]]):format(zero_fill[1], zero_fill[2], zero_fill[3], zero_fill[4], zero_fill[5], zero_fill[6], field_name, field_name),
    guild_id, key, video_url, title, requester_id)
  return key
end

local function bump_affinity(guild_id, user_id, video_url, title, field_name, score_delta)
  local key = track_key(video_url, title)
  score_delta = score_delta or 1.0
  local zero_fill = {}
  for _, c in ipairs(TI_COUNTERS) do zero_fill[#zero_fill + 1] = (c == field_name) and 1 or 0 end
  q(([[
    INSERT INTO harmonic_user_track_affinity (guild_id, user_id, url_key, video_url, title, queued_count, play_count, finish_count, skip_count, like_count, dislike_count, score, last_requested, updated_at)
    VALUES (%%s, %%s, %%s, %%s, %%s, %d, %d, %d, %d, %d, %d, %%s, NOW(), NOW())
    ON CONFLICT (guild_id, user_id, url_key) DO UPDATE SET
      %s = harmonic_user_track_affinity.%s + 1,
      score = harmonic_user_track_affinity.score + %%s,
      video_url = EXCLUDED.video_url, title = EXCLUDED.title, last_requested = NOW(), updated_at = NOW()
  ]]):format(zero_fill[1], zero_fill[2], zero_fill[3], zero_fill[4], zero_fill[5], zero_fill[6], field_name, field_name),
    guild_id, user_id, key, video_url, title, score_delta, score_delta)
  return key
end

local function record_track_queued(guild_id, video_url, title, requester_id)
  bump_track_intelligence(guild_id, video_url, title, requester_id, "queued_count")
  if requester_id then bump_affinity(guild_id, requester_id, video_url, title, "queued_count", 0.5) end
end

local function record_track_play_started(guild_id, video_url, title, requester_id)
  local key = track_key(video_url, title)
  q([[
    INSERT INTO harmonic_track_intelligence (guild_id, url_key, video_url, title, queued_count, play_count, finish_count, skip_count, like_count, dislike_count, total_listen_seconds, last_requester_id, source, first_seen, last_played, updated_at)
    VALUES (%s, %s, %s, %s, 0, 1, 0, 0, 0, 0, 0, %s, 'lavalink', NOW(), NOW(), NOW())
    ON CONFLICT (guild_id, url_key) DO UPDATE SET
      play_count = harmonic_track_intelligence.play_count + 1,
      last_requester_id = EXCLUDED.last_requester_id, last_played = NOW(), updated_at = NOW()
  ]], guild_id, key, video_url, title, requester_id)
  if requester_id then bump_affinity(guild_id, requester_id, video_url, title, "play_count", 1.0) end
end

local function record_track_cooccurrence(guild_id, prev_url, prev_title, next_url, next_title)
  if not (prev_url or prev_title) or not (next_url or next_title) then return end
  local a, b = track_key(prev_url, prev_title), track_key(next_url, next_title)
  if a == b then return end
  q([[
    INSERT INTO harmonic_track_cooccurrence (guild_id, url_key_a, url_key_b, weight, updated_at)
    VALUES (%s, %s, %s, 1, NOW())
    ON CONFLICT (guild_id, url_key_a, url_key_b) DO UPDATE SET
      weight = harmonic_track_cooccurrence.weight + 1, updated_at = NOW()
  ]], guild_id, a, b)
end

local function record_track_outcome(guild_id, video_url, title, requester_id, outcome, listen_seconds)
  local key = track_key(video_url, title)
  local finish_delta = outcome == "finished" and 1 or 0
  local skip_delta = outcome == "skipped" and 1 or 0
  q([[
    INSERT INTO harmonic_track_intelligence (guild_id, url_key, video_url, title, queued_count, play_count, finish_count, skip_count, like_count, dislike_count, total_listen_seconds, first_seen, updated_at)
    VALUES (%s, %s, %s, %s, 0, 0, %s, %s, 0, 0, %s, NOW(), NOW())
    ON CONFLICT (guild_id, url_key) DO UPDATE SET
      finish_count = harmonic_track_intelligence.finish_count + %s,
      skip_count = harmonic_track_intelligence.skip_count + %s,
      total_listen_seconds = harmonic_track_intelligence.total_listen_seconds + %s,
      updated_at = NOW()
  ]], guild_id, key, video_url, title, finish_delta, skip_delta, listen_seconds or 0, finish_delta, skip_delta, listen_seconds or 0)
  if requester_id then
    q([[
      INSERT INTO harmonic_user_track_affinity (guild_id, user_id, url_key, video_url, title, queued_count, play_count, finish_count, skip_count, like_count, dislike_count, score, last_requested, updated_at)
      VALUES (%s, %s, %s, %s, %s, 0, 0, %s, %s, 0, 0, %s, NOW(), NOW())
      ON CONFLICT (guild_id, user_id, url_key) DO UPDATE SET
        finish_count = harmonic_user_track_affinity.finish_count + %s,
        skip_count = harmonic_user_track_affinity.skip_count + %s,
        score = harmonic_user_track_affinity.score + %s,
        updated_at = NOW()
    ]], guild_id, requester_id, key, video_url, title, finish_delta, skip_delta,
       (finish_delta * 1.5 - skip_delta * 1.0), finish_delta, skip_delta, (finish_delta * 1.5 - skip_delta * 1.0))
  end
end

local function record_track_feedback(guild_id, user_id, video_url, title, liked)
  local key = track_key(video_url, title)
  local like_delta = liked and 1 or 0
  local dislike_delta = liked and 0 or 1
  q([[
    INSERT INTO harmonic_track_intelligence (guild_id, url_key, video_url, title, queued_count, play_count, finish_count, skip_count, like_count, dislike_count, total_listen_seconds, first_seen, updated_at)
    VALUES (%s, %s, %s, %s, 0, 0, 0, 0, %s, %s, 0, NOW(), NOW())
    ON CONFLICT (guild_id, url_key) DO UPDATE SET
      like_count = harmonic_track_intelligence.like_count + %s,
      dislike_count = harmonic_track_intelligence.dislike_count + %s,
      updated_at = NOW()
  ]], guild_id, key, video_url, title, like_delta, dislike_delta, like_delta, dislike_delta)
  q([[
    INSERT INTO harmonic_user_track_affinity (guild_id, user_id, url_key, video_url, title, queued_count, play_count, finish_count, skip_count, like_count, dislike_count, score, last_requested, updated_at)
    VALUES (%s, %s, %s, %s, %s, 0, 0, 0, 0, %s, %s, %s, NOW(), NOW())
    ON CONFLICT (guild_id, user_id, url_key) DO UPDATE SET
      like_count = harmonic_user_track_affinity.like_count + %s,
      dislike_count = harmonic_user_track_affinity.dislike_count + %s,
      score = harmonic_user_track_affinity.score + %s,
      updated_at = NOW()
  ]], guild_id, user_id, key, video_url, title, like_delta, dislike_delta, (like_delta * 3.0 - dislike_delta * 4.0),
     like_delta, dislike_delta, (like_delta * 3.0 - dislike_delta * 4.0))
end

-- ============================================================================
-- Lavalink search / track resolution
-- ============================================================================

-- Wraps a Lavalink v4 /v4/loadtracks response into a flat list of "playable"
-- tables ({encoded, uri, title, author, length_ms}) plus playlist info if any.
local function unwrap_load_result(result)
  if not result or not result.loadType then return {}, nil end
  local lt = result.loadType
  if lt == "track" then
    local info = result.data.info
    return { { encoded = result.data.encoded, uri = info.uri, title = info.title, author = info.author, length_ms = info.length } }, nil
  elseif lt == "search" then
    local out = {}
    for _, t in ipairs(result.data or {}) do
      table.insert(out, { encoded = t.encoded, uri = t.info.uri, title = t.info.title, author = t.info.author, length_ms = t.info.length })
    end
    return out, nil
  elseif lt == "playlist" then
    local out = {}
    for _, t in ipairs(result.data.tracks or {}) do
      table.insert(out, { encoded = t.encoded, uri = t.info.uri, title = t.info.title, author = t.info.author, length_ms = t.info.length })
    end
    return out, { name = result.data.info and result.data.info.name }
  elseif lt == "empty" then
    return {}, nil
  elseif lt == "error" then
    return {}, nil, (result.data and result.data.message) or "Lavalink load error"
  end
  return {}, nil
end

-- search_playables(query) -> entries[], playlist_info (or nil), err
local function search_playables(query)
  query = trim(query)
  if query == "" then return {}, nil end
  if not is_explicit_lavalink_query(query) then
    query = "ytmsearch:" .. query
  end
  local result, err = bot.lavalink:load_tracks(query)
  if not result then return {}, nil, err end
  local entries, playlist, load_err = unwrap_load_result(result)
  if load_err then return {}, nil, load_err end
  return entries, playlist
end

-- Resolve a single stored queue url/title back into a playable Lavalink track.
-- Direct URLs are loaded as-is; anything else is re-searched by title so a
-- track that Lavalink previously resolved (e.g. a search-derived stream URL
-- that expired) still plays after a restart.
local function resolve_queue_track(video_url, title)
  local candidate = video_url
  if not candidate or candidate == "" or not is_explicit_lavalink_query(candidate) then
    candidate = "ytmsearch:" .. (title or video_url or "")
  end
  local entries, _playlist, err = search_playables(candidate)
  if entries[1] then return entries[1], candidate end
  if title and title ~= "" then
    entries, _playlist, err = search_playables("ytmsearch:" .. title)
    if entries[1] then return entries[1], "ytmsearch:" .. title end
  end
  return nil, candidate, err or "no results"
end

-- ============================================================================
-- Queue DB helpers (harmonic_queue / harmonic_queue_backup)
-- ============================================================================

local function queue_count(guild_id)
  local row = q1("SELECT COUNT(*) AS c FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic'", guild_id)
  return row and tonumber(row.c) or 0
end

local function backup_count(guild_id)
  local row = q1("SELECT COUNT(*) AS c FROM harmonic_queue_backup WHERE guild_id = %s AND bot_name = 'harmonic'", guild_id)
  return row and tonumber(row.c) or 0
end

local function enqueue_track(guild_id, video_url, title, requester_id, track_uid)
  track_uid = track_uid or new_track_uid()
  q("INSERT INTO harmonic_queue (guild_id, bot_name, video_url, title, requester_id, track_uid) VALUES (%s, 'harmonic', %s, %s, %s, %s)",
    guild_id, video_url, title, requester_id, track_uid)
  q("INSERT INTO harmonic_queue_backup (guild_id, bot_name, video_url, title, requester_id, track_uid) VALUES (%s, 'harmonic', %s, %s, %s, %s) ON CONFLICT DO NOTHING",
    guild_id, video_url, title, requester_id, track_uid)
  record_track_queued(guild_id, video_url, title, requester_id)
  return track_uid
end

local function insert_queue_front(guild_id, video_url, title, requester_id, track_uid)
  track_uid = track_uid or new_track_uid()
  -- Postgres has no auto-increment "insert before everything else" primitive on an
  -- identity PK, so shift by renumbering: give the new row the lowest existing id
  -- minus one via a temp negative offset, then normalize. Simpler and safe here:
  -- select current min id, insert with a manual id one lower isn't possible with
  -- GENERATED ALWAYS AS IDENTITY, so instead we bump every existing row's ordering
  -- by re-keying on a synthetic "sort_at" pattern is overkill for queue sizes this
  -- bot handles -- just delete+reinsert the whole ordered set with the new track
  -- first, which is what the Python bot's insert_queue_front effectively achieves.
  local rows = q("SELECT video_url, title, requester_id, track_uid FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC", guild_id) or {}
  q("DELETE FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic'", guild_id)
  q("INSERT INTO harmonic_queue (guild_id, bot_name, video_url, title, requester_id, track_uid) VALUES (%s, 'harmonic', %s, %s, %s, %s)",
    guild_id, video_url, title, requester_id, track_uid)
  for _, r in ipairs(rows) do
    q("INSERT INTO harmonic_queue (guild_id, bot_name, video_url, title, requester_id, track_uid) VALUES (%s, 'harmonic', %s, %s, %s, %s)",
      guild_id, r.video_url, r.title, r.requester_id, r.track_uid)
  end
  return track_uid
end

local function snapshot_queue_backup(guild_id)
  q("DELETE FROM harmonic_queue_backup WHERE guild_id = %s AND bot_name = 'harmonic'", guild_id)
  q([[
    INSERT INTO harmonic_queue_backup (guild_id, bot_name, video_url, title, requester_id, track_uid)
    SELECT guild_id, bot_name, video_url, title, requester_id, track_uid FROM harmonic_queue
    WHERE guild_id = %s AND bot_name = 'harmonic'
  ]], guild_id)
end

local function delete_backup_track(guild_id, track_uid, video_url, title)
  if track_uid then
    q("DELETE FROM harmonic_queue_backup WHERE guild_id = %s AND bot_name = 'harmonic' AND track_uid = %s", guild_id, track_uid)
    return
  end
  if video_url and title then
    q("DELETE FROM harmonic_queue_backup WHERE ctid IN (SELECT ctid FROM harmonic_queue_backup WHERE guild_id = %s AND bot_name = 'harmonic' AND video_url = %s AND title = %s LIMIT 1)",
      guild_id, video_url, title)
  end
end

-- Fisher-Yates shuffle that keeps the first row pinned (currently-relevant
-- "up next" slot) when preserve_first is true, mirroring shuffle_queue_rows.
local function shuffle_queue_rows(guild_id, preserve_first)
  local rows = q("SELECT id, video_url, title, requester_id, track_uid FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC", guild_id) or {}
  if #rows <= 1 then return #rows end
  local start_idx = preserve_first and 2 or 1
  for i = #rows, start_idx + 1, -1 do
    local j = math.random(start_idx, i)
    rows[i], rows[j] = rows[j], rows[i]
  end
  q("DELETE FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic'", guild_id)
  for _, r in ipairs(rows) do
    q("INSERT INTO harmonic_queue (guild_id, bot_name, video_url, title, requester_id, track_uid) VALUES (%s, 'harmonic', %s, %s, %s, %s)",
      guild_id, r.video_url, r.title, r.requester_id, r.track_uid)
  end
  return #rows
end

local function restore_queue_from_backup(guild_id)
  local rows = q("SELECT video_url, title, requester_id, track_uid FROM harmonic_queue_backup WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC", guild_id) or {}
  if #rows == 0 then return 0 end
  for _, r in ipairs(rows) do
    q("INSERT INTO harmonic_queue (guild_id, bot_name, video_url, title, requester_id, track_uid) VALUES (%s, 'harmonic', %s, %s, %s, %s)",
      guild_id, r.video_url, r.title, r.requester_id, r.track_uid)
  end
  return #rows
end

-- loop_mode == 'queue': finished track goes to the back of the line again.
local function requeue_finished_track(guild_id, video_url, title, requester_id, track_uid)
  enqueue_track(guild_id, video_url, title, requester_id, new_track_uid())
end

-- ============================================================================
-- Audio filter presets (Lavalink v4 /filters JSON). Mirrors apply_filter_preset:
-- each preset REPLACES the active filter set rather than stacking (except the
-- explicit /filter stack= second layer, applied on top by calling this twice).
-- ============================================================================

local FILTER_CHOICES = {
  { name = "None (Standard high quality audio)", value = "none" },
  { name = "Bassboost", value = "bassboost" },
  { name = "Nightcore", value = "nightcore" },
  { name = "Vaporwave", value = "vaporwave" },
  { name = "8D Rotation", value = "8d" },
  { name = "Karaoke", value = "karaoke" },
  { name = "Tremolo", value = "tremolo" },
  { name = "Vibrato", value = "vibrato" },
  { name = "Low Pass", value = "lowpass" },
  { name = "Lo-fi", value = "lofi" },
  { name = "Electronic", value = "electronic" },
  { name = "Party", value = "party" },
  { name = "Radio", value = "radio" },
  { name = "Cinema", value = "cinema" },
  { name = "Soft", value = "soft" },
  { name = "Pop", value = "pop" },
  { name = "Rock", value = "rock" },
  { name = "Classical", value = "classical" },
  { name = "Ear Rape", value = "earrape" },
  { name = "Double Time (2x)", value = "doubletime" },
  { name = "Slow Mo (0.5x)", value = "slowmo" },
  { name = "Pitch Up", value = "pitch_up" },
  { name = "Pitch Down", value = "pitch_down" },
  { name = "Deep", value = "deep" },
  { name = "Anime", value = "anime" },
}
local FILTER_VALUES = {}
local FILTER_LABEL = {}
for _, c in ipairs(FILTER_CHOICES) do FILTER_VALUES[c.value] = true; FILTER_LABEL[c.value] = c.name end

local LOUDNORM_EQ = {
  {0,-0.05},{1,-0.03},{2,0.0},{3,0.0},{4,0.0},{5,0.0},{6,0.0},
  {7,-0.01},{8,-0.02},{9,-0.02},{10,-0.03},{11,-0.02},{12,0.01},{13,0.01},{14,0.0},
}

local function blend_loudnorm(preset_bands)
  local base = {}
  for _, b in ipairs(LOUDNORM_EQ) do base[b[1]] = b[2] end
  for _, b in ipairs(preset_bands) do base[b[1]] = (base[b[1]] or 0) + b[2] end
  local bands = {}
  for band, gain in pairs(base) do table.insert(bands, { band = band, gain = gain }) end
  table.sort(bands, function(a, b) return a.band < b.band end)
  return bands
end

local function eq_bands(list)
  local bands = {}
  for _, b in ipairs(list) do table.insert(bands, { band = b[1], gain = b[2] }) end
  return bands
end

-- apply_filter_preset(filters, mode, current_speed) -> new_speed
-- Mutates `filters` (a plain table matching Lavalink's filters JSON shape) in place.
local function apply_filter_preset(filters, mode, current_speed)
  mode = tostring(mode or "none"):lower():gsub("%s", "")
  local speed = current_speed or 1.0
  local used_eq = false
  if mode == "nightcore" then
    filters.timescale = { speed = 1.25, pitch = 1.3, rate = 1.0 }; speed = 1.25
  elseif mode == "vaporwave" then
    filters.timescale = { speed = 0.8, pitch = 0.8, rate = 1.0 }; speed = 0.8
  elseif mode == "bassboost" then
    used_eq = true; filters.equalizer = blend_loudnorm({ {0,0.32}, {1,0.24}, {2,0.12} })
  elseif mode == "8d" then
    filters.rotation = { rotationHz = 0.18 }
    filters.channelMix = { leftToLeft = 0.8, leftToRight = 0.2, rightToLeft = 0.2, rightToRight = 0.8 }
  elseif mode == "karaoke" then
    filters.karaoke = { level = 1.0, monoLevel = 1.0, filterBand = 220.0, filterWidth = 100.0 }
  elseif mode == "tremolo" then
    filters.tremolo = { frequency = 4.0, depth = 0.45 }
  elseif mode == "vibrato" then
    filters.vibrato = { frequency = 4.5, depth = 0.35 }
  elseif mode == "lowpass" or mode == "lofi" then
    filters.lowPass = { smoothing = mode == "lowpass" and 20.0 or 35.0 }
    if mode == "lofi" then filters.timescale = { speed = 0.94, pitch = 0.96, rate = 1.0 }; speed = 0.94 end
  elseif mode == "electronic" then
    used_eq = true; filters.equalizer = blend_loudnorm({ {0,0.12}, {1,0.10}, {4,-0.05}, {8,0.08}, {10,0.14} })
  elseif mode == "party" then
    used_eq = true; filters.equalizer = blend_loudnorm({ {0,0.25}, {1,0.18}, {2,0.08}, {9,0.10} })
  elseif mode == "radio" then
    used_eq = true; filters.equalizer = blend_loudnorm({ {0,-0.18}, {1,-0.10}, {4,0.12}, {5,0.12}, {10,-0.12} })
    filters.lowPass = { smoothing = 18.0 }
  elseif mode == "cinema" then
    used_eq = true; filters.equalizer = blend_loudnorm({ {0,0.18}, {1,0.12}, {8,0.08}, {9,0.10} })
  elseif mode == "soft" then
    filters.lowPass = { smoothing = 25.0 }
  elseif mode == "pop" then
    used_eq = true
    filters.equalizer = eq_bands({ {0,-0.1},{1,0.1},{2,0.2},{3,0.25},{4,0.2},{5,0.1},{6,0.0},{7,-0.05},{8,-0.1},{9,-0.1},{10,-0.05},{11,0.0},{12,0.1},{13,0.2},{14,0.1} })
  elseif mode == "rock" then
    used_eq = true
    filters.equalizer = eq_bands({ {0,0.3},{1,0.25},{2,0.1},{3,-0.1},{4,-0.15},{5,-0.1},{6,0.0},{7,0.1},{8,0.3},{9,0.35},{10,0.3},{11,0.2},{12,0.1},{13,0.05},{14,0.0} })
  elseif mode == "classical" then
    used_eq = true
    filters.equalizer = eq_bands({ {0,0.1},{1,0.1},{2,0.05},{3,0.0},{4,-0.05},{5,-0.05},{6,-0.05},{7,-0.05},{8,-0.05},{9,-0.05},{10,0.0},{11,0.05},{12,0.1},{13,0.15},{14,0.2} })
  elseif mode == "earrape" then
    filters.distortion = { sinOffset=0.0, sinScale=1.5, cosOffset=0.0, cosScale=1.5, tanOffset=0.0, tanScale=1.0, offset=0.0, scale=1.5 }
  elseif mode == "doubletime" then
    filters.timescale = { speed = 2.0, pitch = 1.0, rate = 1.0 }; speed = 2.0
  elseif mode == "slowmo" then
    filters.timescale = { speed = 0.5, pitch = 1.0, rate = 1.0 }; speed = 0.5
  elseif mode == "pitch_up" then
    filters.timescale = { speed = 1.0, pitch = 1.3, rate = 1.0 }
  elseif mode == "pitch_down" then
    filters.timescale = { speed = 1.0, pitch = 0.7, rate = 1.0 }
  elseif mode == "deep" then
    used_eq = true; filters.equalizer = blend_loudnorm({ {0,0.5}, {1,0.4}, {2,0.3} })
    filters.timescale = { speed = 1.0, pitch = 0.8, rate = 1.0 }
  elseif mode == "anime" then
    filters.timescale = { speed = 1.4, pitch = 1.5, rate = 1.0 }; speed = 1.4
  end
  if not used_eq then filters.equalizer = eq_bands(LOUDNORM_EQ) end
  return speed
end

-- ============================================================================
-- Fade (smooth volume ramp; Harmonic's whole personality hook -- always ramps
-- in small steps instead of a hard cut/pause+jump).
-- ============================================================================

local function fade_curve_progress(progress, curve)
  if curve == "ease_in" then return progress * progress end
  if curve == "ease_out" then return 1 - (1 - progress) * (1 - progress) end
  if curve == "smooth" then return progress * progress * (3 - 2 * progress) end
  return progress -- linear
end

local function fade_volume(guild_id, start_volume, end_volume, duration, curve)
  duration = math.max(0.25, duration or 3.0)
  local steps = math.max(6, math.floor(duration * 10))
  copas.addthread(function()
    for i = 1, steps do
      local progress = fade_curve_progress(i / steps, curve or "smooth")
      local vol = math.floor(start_volume + (end_volume - start_volume) * progress + 0.5)
      bot.lavalink:set_volume(guild_id, clamp(vol, 0, 1000))
      copas.sleep(duration / steps)
    end
    bot.lavalink:set_volume(guild_id, end_volume)
  end)
end

local function choose_fade_duration(mode, configured_seconds, track_duration, filter_mode)
  if mode ~= "smart" then return configured_seconds end
  -- Shorter, gentler ramp for short tracks; a touch longer for long ones;
  -- tighter still under fast filters (nightcore/doubletime/anime) so the
  -- ramp doesn't outlast the filter's own energy.
  local base = 3.0
  if track_duration and track_duration > 0 then
    if track_duration < 90 then base = 1.5
    elseif track_duration > 360 then base = 4.5 end
  end
  if filter_mode == "nightcore" or filter_mode == "doubletime" or filter_mode == "anime" then
    base = math.min(base, 2.0)
  end
  return base
end

-- ============================================================================
-- Voice connection
-- ============================================================================

local function ensure_voice_connection(guild_id, channel_id)
  bot.gateway:join_voice(guild_id, channel_id, false, false)
  -- Give the gateway a moment to hand back VOICE_STATE_UPDATE + VOICE_SERVER_UPDATE
  -- (Bot:_wire_voice_to_lavalink forwards those straight to Lavalink automatically).
  local waited = 0
  while waited < 8 and not (bot.voice_state[guild_id] and bot.voice_state[guild_id].session_id) do
    copas.sleep(0.25)
    waited = waited + 0.25
  end
  -- reconnect_attempts is NOT NULL with no column default (found via real-DB
  -- validation -- every INSERT here must zero-fill it or this fails outright
  -- on the very first /join, same class of bug as the track-intelligence
  -- counters above).
  q([[
    INSERT INTO harmonic_voice_state (guild_id, bot_name, connected_channel_id, last_channel_id, desired_connected, reconnect_attempts, last_seen_at)
    VALUES (%s, 'harmonic', %s, %s, TRUE, 0, NOW())
    ON CONFLICT (guild_id, bot_name) DO UPDATE SET
      connected_channel_id = EXCLUDED.connected_channel_id, last_channel_id = EXCLUDED.last_channel_id,
      desired_connected = TRUE, reconnect_attempts = 0, last_seen_at = NOW(), disconnected_at = NULL
  ]], guild_id, channel_id, channel_id)
  return true
end

local function disconnect_voice(guild_id)
  bot.gateway:leave_voice(guild_id)
  if bot.lavalink.session_id then bot.lavalink:destroy_player(guild_id) end
  q([[
    INSERT INTO harmonic_voice_state (guild_id, bot_name, desired_connected, connected_channel_id, reconnect_attempts, disconnected_at, last_seen_at)
    VALUES (%s, 'harmonic', FALSE, NULL, 0, NOW(), NOW())
    ON CONFLICT (guild_id, bot_name) DO UPDATE SET
      desired_connected = FALSE, connected_channel_id = NULL, disconnected_at = NOW(), last_seen_at = NOW()
  ]], guild_id)
end

-- ============================================================================
-- Feedback / status messaging
-- ============================================================================

local function feedback_channel_id(guild_id)
  local settings = get_guild_settings(guild_id)
  return settings.feedback_channel_id
end

local function send_feedback(guild_id, e, dedupe_key)
  local ch = feedback_channel_id(guild_id)
  if not ch then return end
  if dedupe_key then
    local exp = feedback_dedupe[dedupe_key]
    if exp and exp > now() then return end
    feedback_dedupe[dedupe_key] = now() + 20
  end
  bot.rest:post(("/channels/%s/messages"):format(ch), { embeds = { e } })
end

-- ============================================================================
-- Current-track snapshot / position tracking
-- ============================================================================

local function current_track_position(guild_id)
  local data = playback_tracking[guild_id]
  if not data then return 0 end
  if data.paused then return math.floor(data.offset or 0) end
  local speed = data.speed or 1.0
  local elapsed = (mono() - (data.start_time or mono())) * speed
  local pos = (data.offset or 0) + elapsed
  if data.duration and data.duration > 0 then pos = math.min(pos, data.duration) end
  return math.floor(math.max(0, pos))
end

local function get_current_track_snapshot(guild_id)
  local data = playback_tracking[guild_id]
  if not data then return nil end
  return { url = data.url, title = data.title, track_uid = data.track_uid, requester_id = data.requester_id }
end

-- ============================================================================
-- Auto-DJ: Smart recommendation engine
-- ============================================================================

local SMART_RECENCY_HALFLIFE_DAYS = 21
local SMART_SEED_POOL_LIMIT = 25
local AUTODJ_MIN_INTERVAL_SECONDS = 20
local AUTODJ_FAILURE_BACKOFF_SECONDS = 60

local function get_autodj_enabled(guild_id)
  local row = q1("SELECT auto_dj FROM harmonic_swarm_toggles WHERE guild_id = %s", guild_id)
  return row ~= nil and row.auto_dj == true
end

local function set_autodj_enabled(guild_id, enabled)
  q([[
    INSERT INTO harmonic_swarm_toggles (guild_id, auto_dj) VALUES (%s, %s)
    ON CONFLICT (guild_id) DO UPDATE SET auto_dj = EXCLUDED.auto_dj
  ]], guild_id, enabled)
end

-- Builds a weighted candidate pool from (in priority order): the listeners'
-- personal affinity scores, server-wide track intelligence, and "what usually
-- plays next" cooccurrence off the most recently played track. Falls back to
-- recent history, then a canned mood search. This is a direct SQL port of
-- build_smart_recommendation's weighting formula (recency-decayed via
-- POW(0.5, days/halflife)), minus the embedding-similarity layer (no vector
-- embedding service in this stack -- see report).
local function build_smart_recommendation(guild_id, listener_ids)
  local candidates = {}
  local decay = ("POWER(0.5, LEAST(GREATEST(EXTRACT(DAY FROM (NOW() - COALESCE(last_requested, NOW()))), 0), 365) / %d)"):format(SMART_RECENCY_HALFLIFE_DAYS)
  local server_decay = ("POWER(0.5, LEAST(GREATEST(EXTRACT(DAY FROM (NOW() - COALESCE(last_played, last_queued, first_seen))), 0), 365) / %d)"):format(SMART_RECENCY_HALFLIFE_DAYS)

  if listener_ids and #listener_ids > 0 then
    local placeholders = {}
    for i = 1, #listener_ids do placeholders[i] = "%s" end
    local sql = ([[
      SELECT title, video_url,
             (score + play_count * 1.35 + finish_count * 1.5 + like_count * 3.0 - dislike_count * 4.0
              - (skip_count::float / (play_count + finish_count + 1)) * 6.0) * %s AS weight,
             'listener taste' AS reason
      FROM harmonic_user_track_affinity
      WHERE guild_id = %%s AND user_id IN (%s) AND (dislike_count <= like_count OR like_count > 0)
      ORDER BY weight DESC, last_requested DESC LIMIT %d
    ]]):format(decay, table.concat(placeholders, ","), SMART_SEED_POOL_LIMIT)
    local rows = q(sql, guild_id, unpack(listener_ids)) or {}
    for _, r in ipairs(rows) do table.insert(candidates, r) end
  end

  local rows = q(([[
    SELECT title, video_url,
           (play_count * 1.1 + finish_count * 1.6 + like_count * 3.0 + queued_count * 0.2 - dislike_count * 4.0
            - (skip_count::float / (play_count + finish_count + 1)) * 5.0) * %s AS weight,
           'server taste' AS reason
    FROM harmonic_track_intelligence
    WHERE guild_id = %%s AND (dislike_count <= like_count OR like_count > 0)
    ORDER BY weight DESC LIMIT %d
  ]]):format(server_decay, SMART_SEED_POOL_LIMIT), guild_id) or {}
  for _, r in ipairs(rows) do table.insert(candidates, r) end

  local last = q1("SELECT video_url, title FROM harmonic_history WHERE guild_id = %s ORDER BY played_at DESC LIMIT 1", guild_id)
  if last then
    local last_key = track_key(last.video_url, last.title)
    rows = q([[
      SELECT ti.title AS title, ti.video_url AS video_url, (tc.weight * 2.0) AS weight, 'often played next' AS reason
      FROM harmonic_track_cooccurrence tc
      JOIN harmonic_track_intelligence ti ON ti.guild_id = tc.guild_id AND ti.url_key = tc.url_key_b
      WHERE tc.guild_id = %s AND tc.url_key_a = %s AND (ti.dislike_count <= ti.like_count OR ti.like_count > 0)
      ORDER BY tc.weight DESC LIMIT 8
    ]], guild_id, last_key) or {}
    for _, r in ipairs(rows) do table.insert(candidates, r) end
  end

  if #candidates == 0 then
    rows = q("SELECT title, video_url, 1.0 AS weight, 'recent history' AS reason FROM harmonic_history WHERE guild_id = %s ORDER BY played_at DESC LIMIT %d", guild_id, SMART_SEED_POOL_LIMIT) or {}
    for _, r in ipairs(rows) do table.insert(candidates, r) end
  end

  if #candidates == 0 then
    local fallbacks = { "lofi hip hop", "synthwave mix", "chill electronic", "gaming music", "jazz hop" }
    local term = fallbacks[math.random(1, #fallbacks)]
    return { query = "ytmsearch:" .. term, seed_title = term, seed_url = nil, reason = "fallback" }
  end

  -- weighted random pick
  local total = 0
  for _, c in ipairs(candidates) do total = total + math.max(0, tonumber(c.weight) or 0) end
  local seed
  if total <= 0 then
    seed = candidates[math.random(1, #candidates)]
  else
    local roll = math.random() * total
    local acc = 0
    for _, c in ipairs(candidates) do
      acc = acc + math.max(0, tonumber(c.weight) or 0)
      if roll <= acc then seed = c; break end
    end
    seed = seed or candidates[#candidates]
  end

  return { query = "ytmsearch:" .. tostring(seed.title or ""), seed_title = seed.title, seed_url = seed.video_url, reason = seed.reason }
end

local function load_smart_avoid_keys(guild_id, listener_ids)
  local avoid = {}
  local rows = q("SELECT url_key FROM harmonic_track_intelligence WHERE guild_id = %s AND dislike_count > like_count", guild_id) or {}
  for _, r in ipairs(rows) do avoid[r.url_key] = true end
  if listener_ids and #listener_ids > 0 then
    local placeholders = {}
    for i = 1, #listener_ids do placeholders[i] = "%s" end
    rows = q(("SELECT url_key FROM harmonic_user_track_affinity WHERE guild_id = %%s AND user_id IN (%s) AND dislike_count > like_count"):format(table.concat(placeholders, ",")),
      guild_id, unpack(listener_ids)) or {}
    for _, r in ipairs(rows) do avoid[r.url_key] = true end
  end
  return avoid
end

local function pick_smart_recommendation_track(guild_id, listener_ids)
  local recommendation = build_smart_recommendation(guild_id, listener_ids)
  local avoid = load_smart_avoid_keys(guild_id, listener_ids)
  local entries = search_playables(recommendation.query)
  local chosen
  local scanned = 0
  for _, entry in ipairs(entries) do
    scanned = scanned + 1
    if entry.title or entry.uri then
      if not avoid[track_key(entry.uri, entry.title)] or scanned >= 8 then
        chosen = entry
        break
      end
    end
  end
  if not chosen then chosen = entries[1] end
  return chosen, recommendation
end

local function record_smart_recommendation(guild_id, requester_id, recommendation, chosen, reason)
  q([[
    INSERT INTO harmonic_smart_recommendations (guild_id, requester_id, seed_title, seed_url, query_text, chosen_url, chosen_title, reason, accepted, created_at)
    VALUES (%s, %s, %s, %s, %s, %s, %s, %s, TRUE, NOW())
  ]], guild_id, requester_id, recommendation.seed_title, recommendation.seed_url, recommendation.query,
     chosen and chosen.uri, chosen and chosen.title, reason or recommendation.reason)
end

-- Best-effort: when the queue runs dry and Auto-DJ is enabled for this guild,
-- pick and enqueue one smart recommendation. Returns true if it queued something.
local function maybe_enqueue_autodj(guild_id, channel_id)
  local until_time = autodj_fail_until[guild_id] or 0
  if mono() < until_time then return false end
  if not get_autodj_enabled(guild_id) then return false end
  local listener_ids = channel_member_ids(guild_id, channel_id)
  local ok, chosen, recommendation = pcall(pick_smart_recommendation_track, guild_id, listener_ids)
  if not ok or not chosen then
    autodj_fail_until[guild_id] = mono() + AUTODJ_FAILURE_BACKOFF_SECONDS
    return false
  end
  enqueue_track(guild_id, chosen.uri, chosen.title, bot.user_id)
  record_smart_recommendation(guild_id, bot.user_id, recommendation, chosen, "autodj")
  return true
end

-- ============================================================================
-- Playback state persistence
-- ============================================================================

local function persist_playback_state(guild_id, channel_id, video_url, title, position, playing, paused, track_uid)
  q([[
    INSERT INTO harmonic_playback_state (guild_id, bot_name, channel_id, video_url, position_seconds, is_playing, is_paused, title, play_session_key, track_uid, last_checkpoint_at)
    VALUES (%s, 'harmonic', %s, %s, %s, %s, %s, %s, %s, %s, NOW())
    ON CONFLICT (guild_id, bot_name) DO UPDATE SET
      channel_id = EXCLUDED.channel_id, video_url = EXCLUDED.video_url, position_seconds = EXCLUDED.position_seconds,
      is_playing = EXCLUDED.is_playing, is_paused = EXCLUDED.is_paused, title = EXCLUDED.title,
      play_session_key = EXCLUDED.play_session_key, track_uid = EXCLUDED.track_uid, last_checkpoint_at = NOW()
  ]], guild_id, channel_id, video_url, math.floor(position or 0), playing, paused, title, track_uid, track_uid)
end

local function clear_playback_state(guild_id)
  q([[
    UPDATE harmonic_playback_state SET channel_id = NULL, video_url = NULL, title = NULL, position_seconds = 0,
      is_playing = FALSE, is_paused = FALSE, play_session_key = NULL, track_uid = NULL
    WHERE guild_id = %s AND bot_name = 'harmonic'
  ]], guild_id)
end

-- ============================================================================
-- Core playback engine (process_queue)
-- ============================================================================

local channel_kind_cache = {} -- channel_id -> "stage" | "voice"
local last_stage_topic = {}   -- guild_id -> last topic string sent (dedup)

local function get_channel_kind(channel_id)
  if not channel_id then return "voice" end
  local cached = channel_kind_cache[channel_id]
  if cached then return cached end
  local ch = bot.rest:get("/channels/" .. tostring(channel_id))
  local kind = (ch and ch.type == 13) and "stage" or "voice"
  channel_kind_cache[channel_id] = kind
  return kind
end

local function update_stage_topic(guild_id, channel_id, title)
  if not channel_id then return end
  local ok, err = pcall(function()
    local safe_title = tostring(title or "Unknown Track"):gsub("\n", " "):sub(1, 60)
    local topic = "\xF0\x9F\x8E\xB5 " .. safe_title
    if last_stage_topic[guild_id] == topic then return end
    if get_channel_kind(channel_id) == "stage" then
      local patched = bot.rest:patch("/stage-instances/" .. tostring(channel_id), { topic = topic })
      if not patched then
        bot.rest:post("/stage-instances", { channel_id = tostring(channel_id), topic = topic, privacy_level = 2 })
      end
    else
      bot.rest:patch("/channels/" .. tostring(channel_id), { status = topic })
    end
    last_stage_topic[guild_id] = topic
  end)
  if not ok then print(("[harmonic] stage/voice topic update failed for %s: %s"):format(tostring(guild_id), tostring(err))) end
end

local function clear_stage_topic(guild_id, channel_id)
  last_stage_topic[guild_id] = nil
  if not channel_id then return end
  pcall(function()
    if get_channel_kind(channel_id) == "stage" then
      bot.rest:delete("/stage-instances/" .. tostring(channel_id))
    else
      bot.rest:patch("/channels/" .. tostring(channel_id), { status = cjson.null })
    end
  end)
end

local function should_auto_disconnect(guild_id, channel_id, stay_in_vc)
  if stay_in_vc then return false end
  local listeners = channel_human_listeners(guild_id, channel_id)
  return #listeners == 0
end

local process_queue -- forward decl (self-referential via track-end handler)

local function process_queue_inner(guild_id, channel_id, start_position)
  start_position = start_position or 0
  local settings = get_guild_settings(guild_id)
  local volume = settings.volume or 100
  local loop_mode = settings.loop_mode or "queue"
  local filter_mode = settings.filter_mode or "none"
  local filter_stack = settings.filter_stack
  local trans_mode = settings.transition_mode or "off"
  local c_speed = settings.custom_speed or 1.0
  local c_pitch = settings.custom_pitch or 1.0
  local c_mod_left = settings.custom_modifiers_left or 0
  local stay_in_vc = settings.stay_in_vc or false
  local fade_seconds = clamp(settings.fade_seconds or 3.0, 0.25, 12.0)
  local fade_curve = settings.fade_curve or "smooth"

  local next_song = q1("SELECT id, video_url, title, requester_id, track_uid FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC LIMIT 1", guild_id)

  if not next_song then
    local restored = 0
    if loop_mode == "queue" then
      restored = restore_queue_from_backup(guild_id)
      if restored > 0 then shuffle_queue_rows(guild_id, true) end
    end
    if restored > 0 then
      next_song = q1("SELECT id, video_url, title, requester_id, track_uid FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC LIMIT 1", guild_id)
    end
  end

  if not next_song then
    clear_playback_state(guild_id)
    playback_tracking[guild_id] = nil
    guild_states[guild_id] = nil
    if loop_mode ~= "queue" then
      q("DELETE FROM harmonic_queue_backup WHERE guild_id = %s AND bot_name = 'harmonic'", guild_id)
    end
    if maybe_enqueue_autodj(guild_id, channel_id) then
      return process_queue(guild_id, channel_id)
    end
    if should_auto_disconnect(guild_id, channel_id, stay_in_vc) then
      clear_stage_topic(guild_id, channel_id)
      disconnect_voice(guild_id)
    end
    return
  end

  local song_id, url, title, requester_id, track_uid = next_song.id, next_song.video_url, next_song.title, next_song.requester_id, next_song.track_uid
  track_uid = track_uid or new_track_uid()
  local original_url, original_title = url, title
  q("DELETE FROM harmonic_queue WHERE id = %s AND guild_id = %s AND bot_name = 'harmonic'", song_id, guild_id)

  local track, resolved_source
  local cached = prefetch_cache[guild_id]
  if cached and cached.url == url and cached.expires_at > mono() then
    track = cached.track
    prefetch_cache[guild_id] = nil
  else
    track, resolved_source = resolve_queue_track(url, title)
  end

  if not track then
    print(("[harmonic] [%s] Lavalink search failed for '%s'"):format(tostring(guild_id), tostring(title)))
    -- Put it back at the tail of recovery instead of losing it silently.
    enqueue_track(guild_id, url, title, requester_id, track_uid)
    q("DELETE FROM harmonic_queue WHERE id = (SELECT id FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' AND track_uid = %s ORDER BY id DESC LIMIT 1)", guild_id, track_uid)
    -- avoid a tight failure loop: brief pause then move on to whatever's next
    copas.sleep(1.0)
    return process_queue(guild_id, channel_id)
  end
  url = track.uri or url
  title = track.title or title
  local duration = (track.length_ms or 0) / 1000
  local uploader = track.author or "Unknown"

  local ok = ensure_voice_connection(guild_id, channel_id)
  if not ok then
    print(("[harmonic] [%s] Voice connection unavailable; requeueing '%s'"):format(tostring(guild_id), tostring(title)))
    enqueue_track(guild_id, url, title, requester_id, track_uid)
    return
  end

  local filters = {}
  bot.lavalink:set_volume(guild_id, volume)

  if c_mod_left > 0 then
    filters.timescale = { speed = c_speed, pitch = c_pitch, rate = 1.0 }
    c_mod_left = c_mod_left - 1
    q("UPDATE harmonic_guild_settings SET custom_modifiers_left = %s WHERE guild_id = %s", c_mod_left, guild_id)
    if c_mod_left == 0 then
      q("UPDATE harmonic_guild_settings SET custom_speed = 1.0, custom_pitch = 1.0 WHERE guild_id = %s", guild_id)
    end
  end

  c_speed = apply_filter_preset(filters, filter_mode, c_speed)
  if filter_stack and filter_stack ~= filter_mode and filter_stack ~= cjson.null then
    c_speed = apply_filter_preset(filters, filter_stack, c_speed)
  end
  bot.lavalink:update_player(guild_id, { filters = filters })

  local should_fade = (trans_mode == "fade" or trans_mode == "smart" or trans_mode == "mix") and start_position <= 0
  if should_fade then bot.lavalink:set_volume(guild_id, 0) end

  local play_start_ms = math.floor(math.max(0, start_position) * 1000)
  local play_ok, play_err = bot.lavalink:update_player(guild_id, {
    encodedTrack = track.encoded,
    position = play_start_ms > 0 and play_start_ms or nil,
  })
  if not play_ok then
    print(("[harmonic] [%s] Playback start failed for '%s': %s"):format(tostring(guild_id), tostring(title), tostring(play_err)))
    enqueue_track(guild_id, url, title, requester_id, track_uid)
    return
  end

  update_stage_topic(guild_id, channel_id, title)

  local prev_track = playback_tracking[guild_id]
  playback_tracking[guild_id] = {
    start_time = mono(), offset = start_position, url = url, title = title, duration = duration,
    channel_id = channel_id, track_uid = track_uid, original_queue_url = original_url, original_queue_title = original_title,
    speed = c_speed, current_filter = filter_mode, requester_id = requester_id, transition_mode = trans_mode,
    volume = volume, paused = false, listen_committed = 0,
  }
  guild_states[guild_id] = { voice_channel_id = channel_id, position = start_position, track_uid = track_uid, url = url, title = title }

  if should_fade then
    local fd = choose_fade_duration(trans_mode, fade_seconds, duration, filter_mode)
    fade_volume(guild_id, 0, volume, fd, fade_curve)
  end

  -- Prefetch what's coming up next so the next process_queue call has near-zero gap.
  local nxt = q1("SELECT video_url, title FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC LIMIT 1", guild_id)
  if nxt and nxt.video_url then
    copas.addthread(function()
      local t = resolve_queue_track(nxt.video_url, nxt.title)
      if t then prefetch_cache[guild_id] = { url = nxt.video_url, track = t, expires_at = mono() + 300 } end
    end)
  end

  if start_position <= 0 then
    q("INSERT INTO harmonic_history (guild_id, video_url, title, requester_id) VALUES (%s, %s, %s, %s)", guild_id, url, title, requester_id)
    record_track_play_started(guild_id, url, title, requester_id)
    if prev_track and (prev_track.url or prev_track.title) then
      record_track_cooccurrence(guild_id, prev_track.url, prev_track.title, url, title)
    end
  end

  persist_playback_state(guild_id, channel_id, url, title, start_position, true, false, track_uid)

  local e = embed({
    title = "🎵 Now Playing", color = 0x5865F2,
    description = ("**[%s](%s)**\n*By: %s*"):format(title, url, uploader),
    fields = { field("Track ID", "`" .. track_uid_label(track_uid) .. "`", true) },
  })
  if requester_id then
    table.insert(e.fields, field("Requested by", resolve_requester_name(guild_id, requester_id), true))
  end
  if TRACK_FEEDBACK_BROADCAST then
    send_feedback(guild_id, e, "now_playing:" .. track_uid)
  end
end

process_queue = function(guild_id, channel_id, start_position)
  if processing_guild[guild_id] then return end
  processing_guild[guild_id] = true
  local ok, err = pcall(process_queue_inner, guild_id, channel_id, start_position)
  processing_guild[guild_id] = false
  if not ok then
    print(("[harmonic] process_queue error for guild %s: %s"):format(tostring(guild_id), tostring(err)))
    report_error(guild_id, "runtime", "process_queue error", tostring(err))
  end
end

local function stop_playback(guild_id)
  local data = playback_tracking[guild_id]
  local channel_id = (data and data.channel_id) or (guild_states[guild_id] and guild_states[guild_id].voice_channel_id) or get_home_channel_id(guild_id)
  clear_stage_topic(guild_id, channel_id)
  playback_tracking[guild_id] = nil
  guild_states[guild_id] = nil
  if bot.lavalink.session_id then bot.lavalink:stop(guild_id) end
  clear_playback_state(guild_id)
end

-- ============================================================================
-- Lavalink websocket event wiring: TrackStartEvent / TrackEndEvent /
-- TrackExceptionEvent / TrackStuckEvent / WebSocketClosedEvent, plus
-- playerUpdate for live position tracking.
-- ============================================================================

bot.lavalink:on("event", function(msg)
  local guild_id = msg.guildId
  if not guild_id then return end

  if msg.type == "TrackStartEvent" then
    -- Nothing to do -- playback_tracking was already seeded by process_queue
    -- right before the play() call landed.
    return
  end

  if msg.type == "TrackEndEvent" then
    if msg.reason == "replaced" then return end
    local data = playback_tracking[guild_id]
    local track_uri = (data and (data.original_queue_url or data.url))
    local track_title = (data and (data.original_queue_title or data.title))
    local requester_id = data and data.requester_id
    local track_uid = data and data.track_uid
    local final_position = msg.reason == "finished" and math.floor((data and data.duration) or current_track_position(guild_id) or 0)
      or current_track_position(guild_id)
    local outcome = msg.reason == "finished" and "finished" or "skipped"

    local settings = get_guild_settings(guild_id)
    local loop_mode = settings.loop_mode or "queue"

    if track_uri or track_title then
      record_track_outcome(guild_id, track_uri, track_title, requester_id, outcome, final_position)
    end

    if msg.reason == "finished" then
      if loop_mode == "queue" then
        requeue_finished_track(guild_id, track_uri, track_title, requester_id, track_uid)
      elseif loop_mode == "song" then
        insert_queue_front(guild_id, track_uri, track_title, requester_id, track_uid)
      else
        delete_backup_track(guild_id, track_uid, track_uri, track_title)
      end
    else
      delete_backup_track(guild_id, track_uid, track_uri, track_title)
    end

    local channel_id = (data and data.channel_id) or (guild_states[guild_id] and guild_states[guild_id].voice_channel_id)
    if channel_id and (msg.reason == "finished" or msg.reason == "stopped" or msg.reason == "loadFailed" or msg.reason == "cleanup") then
      copas.addthread(function() process_queue(guild_id, channel_id) end)
    end
    return
  end

  if msg.type == "TrackExceptionEvent" or msg.type == "TrackStuckEvent" then
    print(("[harmonic] [%s] %s: %s"):format(tostring(guild_id), msg.type, tostring(msg.exception and msg.exception.message or msg.type)))
    local data = playback_tracking[guild_id]
    local channel_id = (data and data.channel_id) or (guild_states[guild_id] and guild_states[guild_id].voice_channel_id)
    if channel_id then
      copas.addthread(function() process_queue(guild_id, channel_id) end)
    end
    return
  end

  if msg.type == "WebSocketClosedEvent" then
    print(("[harmonic] [%s] Voice websocket closed (code=%s)"):format(tostring(guild_id), tostring(msg.code)))
    return
  end
end)

bot.lavalink:on("playerUpdate", function(msg)
  local guild_id = msg.guildId
  local data = guild_id and playback_tracking[guild_id]
  if not data or not msg.state then return end
  if msg.state.position ~= nil then
    data.offset = msg.state.position / 1000
    data.start_time = mono()
  end
end)

-- ============================================================================
-- Small shared UI/behavior helpers used across several commands
-- ============================================================================

local function make_progress_bar(current, total, length)
  length = length or 15
  current = math.floor(current or 0)
  if not total or total <= 0 then
    return ("[%s] %d:%02d / Live"):format(("▬"):rep(length), math.floor(current / 60), current % 60)
  end
  total = math.floor(total)
  local progress = clamp(math.floor((current / total) * length), 0, length)
  local bar = ("▬"):rep(progress) .. "🔘" .. ("▬"):rep(math.max(0, length - progress - 1))
  return ("[%s] %d:%02d / %d:%02d"):format(bar, math.floor(current / 60), current % 60, math.floor(total / 60), total % 60)
end

-- Resolve the channel a command should act on: saved home channel first (this
-- mirrors the Python bot's "home channel takes priority" behavior), else the
-- invoking user's current voice channel.
local function resolve_target_channel(interaction)
  local home = get_home_channel_id(interaction.guild_id)
  if home then return home end
  local vs = voice_states[interaction.guild_id] and voice_states[interaction.guild_id][interaction.member.user.id]
  return vs and vs.channel_id
end

local function invoker_voice_channel(interaction)
  local vs = voice_states[interaction.guild_id] and voice_states[interaction.guild_id][interaction.member.user.id]
  return vs and vs.channel_id
end

local function sync_pause_state(guild_id, paused)
  local data = playback_tracking[guild_id]
  if data then
    if paused then
      data.offset = current_track_position(guild_id)
    else
      data.start_time = mono()
    end
    data.paused = paused
  end
  q("UPDATE harmonic_playback_state SET is_paused = %s WHERE guild_id = %s AND bot_name = 'harmonic'", paused, guild_id)
end

local function player_is_active(guild_id)
  return playback_tracking[guild_id] ~= nil
end

-- Lightweight lyrics lookup against LRCLIB (public, no API key -- same
-- provider harmonic.py used for /lyrics).
local function fetch_lyrics(title)
  title = trim(title)
  if title == "" then return nil end
  local response_body = {}
  local ok = https.request({
    url = "https://lrclib.net/api/search?q=" .. title:gsub(" ", "%%20"),
    method = "GET",
    headers = { ["User-Agent"] = "swarmlua-harmonic/1.0" },
    sink = ltn12.sink.table(response_body),
  })
  if not ok then return nil end
  local raw = table.concat(response_body)
  local ok2, results = pcall(cjson.decode, raw)
  if not ok2 or type(results) ~= "table" or #results == 0 then return nil end
  local best = results[1]
  return {
    plain = best.plainLyrics,
    synced_raw = best.syncedLyrics,
    track_name = best.trackName,
    artist_name = best.artistName,
  }
end

local function parse_synced_lyrics(lrc)
  local lines = {}
  if not lrc then return lines end
  for line in lrc:gmatch("[^\r\n]+") do
    local mm, ss, ms, text = line:match("%[(%d+):(%d+)%.?(%d*)%](.*)")
    if mm then
      local ts = tonumber(mm) * 60 + tonumber(ss) + (tonumber("0." .. ms) or 0)
      text = trim(text)
      if text ~= "" then table.insert(lines, { ts = ts, text = text }) end
    end
  end
  table.sort(lines, function(a, b) return a.ts < b.ts end)
  return lines
end

-- ============================================================================
-- Commands: Server configuration
-- ============================================================================

bot:command(PREFIX .. "sethome", {
  description = "Save this bot's default voice or stage channel for join, autoplay, and recovery behavior.",
  options = {{ type = 7, name = "channel", description = "Voice or stage channel", required = true, channel_types = { 2, 13 } }},
}, function(self, interaction)
  if not member_is_admin(interaction) then return reply_text(interaction, "Administrator only.", true) end
  local channel_id = opt_value(interaction, "channel")
  q([[
    INSERT INTO harmonic_bot_home_channels (guild_id, bot_name, home_vc_id) VALUES (%s, 'harmonic', %s)
    ON CONFLICT (guild_id, bot_name) DO UPDATE SET home_vc_id = EXCLUDED.home_vc_id
  ]], interaction.guild_id, channel_id)
  reply(interaction, embed({ title = "🏠 Home Set", description = ("Home channel set to <#%s>."):format(channel_id), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "setfeedback", {
  description = "Choose the text channel (or thread) for updates, queue actions, and recovery notices.",
  options = {{ type = 7, name = "channel", description = "Text channel or thread", required = true, channel_types = { 0, 5, 10, 11, 12 } }},
}, function(self, interaction)
  if not member_is_admin(interaction) then return reply_text(interaction, "Administrator only.", true) end
  local channel_id = opt_value(interaction, "channel")
  set_guild_setting(interaction.guild_id, "feedback_channel_id", channel_id)
  reply(interaction, embed({ title = "✅ Feedback Channel Set", description = ("Updates will be sent to <#%s>."):format(channel_id), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "djrole", {
  description = "Set the server DJ role that can manage restricted playback, queue, and settings commands.",
  options = {{ type = 8, name = "role", description = "DJ role", required = true }},
}, function(self, interaction)
  if not member_is_admin(interaction) then return reply_text(interaction, "Administrator only.", true) end
  local role_id = opt_value(interaction, "role")
  set_guild_setting(interaction.guild_id, "dj_role_id", role_id)
  reply(interaction, embed({ description = ("🎧 DJ role set to <@&%s>"):format(role_id), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "removedj", {
  description = "Clear the configured DJ role so only admins or open-access mode can control restricted commands.",
}, function(self, interaction)
  if not member_is_admin(interaction) then return reply_text(interaction, "Administrator only.", true) end
  set_guild_setting(interaction.guild_id, "dj_role_id", nil)
  reply(interaction, embed({ description = "DJ role requirements removed.", color = COLOR.green }), true)
end)

bot:command(PREFIX .. "djmode", {
  description = "Enable or disable Strict DJ Mode so only admins and the DJ role can use control commands.",
}, function(self, interaction)
  if not member_is_admin(interaction) then return reply_text(interaction, "Administrator only.", true) end
  local settings = get_guild_settings(interaction.guild_id)
  local new_val = not (settings.dj_only_mode == true)
  set_guild_setting(interaction.guild_id, "dj_only_mode", new_val)
  reply(interaction, embed({ description = ("🎧 Strict DJ Mode is now **%s**."):format(new_val and "ENABLED" or "DISABLED"), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "247", {
  description = "Keep the bot connected and ready in voice channels even after playback ends until you disable it.",
}, function(self, interaction)
  if not member_is_admin(interaction) then return reply_text(interaction, "Administrator only.", true) end
  local settings = get_guild_settings(interaction.guild_id)
  local new_val = not (settings.stay_in_vc == true)
  set_guild_setting(interaction.guild_id, "stay_in_vc", new_val)
  reply(interaction, embed({ description = ("🕰️ 24/7 Mode is now **%s**."):format(new_val and "ENABLED" or "DISABLED"), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "restart", {
  description = "Restart this bot instance immediately for maintenance or recovery. Administrator only.",
}, function(self, interaction)
  if not member_is_admin(interaction) then return reply_text(interaction, "Administrator only.", true) end
  reply_text(interaction, "Restarting...", true)
  print("[harmonic] Restart requested via /harmonic_main_restart; exiting for supervisor restart.")
  copas.addthread(function() copas.sleep(1); os.exit(0) end)
end)

bot:command(PREFIX .. "settings", {
  description = "Show the saved playback, DJ, queue, and recovery settings for this server",
}, function(self, interaction)
  defer(interaction, true)
  local s = get_guild_settings(interaction.guild_id)
  local autodj_state = get_autodj_enabled(interaction.guild_id)
  local e = embed({ title = "⚙️ Server Music Settings", color = COLOR.blurple, fields = {
    field("Home Channel", s.home_vc_id and ("<#" .. s.home_vc_id .. ">") or "Not set", true),
    field("Feedback Channel", s.feedback_channel_id and ("<#" .. s.feedback_channel_id .. ">") or "Not set", true),
    field("DJ Role", s.dj_role_id and ("<@&" .. s.dj_role_id .. ">") or "Not set", true),
    field("Volume", s.volume or 100, true),
    field("Loop Mode", s.loop_mode or "queue", true),
    field("Filter", s.filter_mode or "none", true),
    field("Transitions", s.transition_mode or "off", true),
    field("Custom Speed/Pitch", ("%sx / %sx (%s left)"):format(s.custom_speed or 1.0, s.custom_pitch or 1.0, s.custom_modifiers_left or 0), true),
    field("Strict DJ", s.dj_only_mode and "Enabled" or "Disabled", true),
    field("24/7 Mode", s.stay_in_vc and "Enabled" or "Disabled", true),
    field("Auto-DJ", autodj_state and "Enabled" or "Disabled", true),
  }})
  followup(interaction, e, true)
end)

-- ============================================================================
-- Commands: Playback & transport
-- ============================================================================

bot:command(PREFIX .. "play", {
  description = "Queue a track, URL, livestream, search result, or playlist and start playback if idle.",
  options = {
    { type = 3, name = "search", description = "Track name, URL, or search text", required = true, autocomplete = true },
    { type = 3, name = "source", description = "Where to search (defaults to YouTube for plain text)", required = false,
      choices = { { name = "YouTube", value = "ytmsearch" }, { name = "SoundCloud", value = "scsearch" } } },
  },
}, function(self, interaction)
  local search = opt_value(interaction, "search", "")
  local source = opt_value(interaction, "source", "ytmsearch")
  if (source == "ytmsearch" or source == "scsearch") and not is_explicit_lavalink_query(search) then
    search = source .. ":" .. search
  end
  defer(interaction, false)

  local channel_id = resolve_target_channel(interaction)
  if not channel_id then
    return followup(interaction, embed({ title = "❌ Error", description = "Join a channel first or set a home channel.", color = COLOR.red }))
  end

  local entries, playlist, err = search_playables(search)
  if not entries or #entries == 0 then
    return followup(interaction, embed({ title = "❌ Source Error", description = "Could not load that source: " .. tostring(err or "nothing playable came back"), color = COLOR.red }))
  end

  local requester_id = interaction.member.user.id
  for _, t in ipairs(entries) do
    enqueue_track(interaction.guild_id, t.uri, t.title, requester_id, new_track_uid())
  end
  if #entries > 1 then shuffle_queue_rows(interaction.guild_id, true) end

  local was_idle = not player_is_active(interaction.guild_id)
  if was_idle then
    followup(interaction, embed({ title = "🎶 Queued & Starting", description = ("Added **%d** track(s). Starting Lavalink Engine!"):format(#entries), color = COLOR.green }))
    copas.addthread(function() process_queue(interaction.guild_id, channel_id) end)
  else
    followup(interaction, embed({ title = "📥 Added to Queue", description = ("Added **%d** track(s). (Queue size: %d)"):format(#entries, queue_count(interaction.guild_id)), color = COLOR.blue }))
  end
end)

bot:command(PREFIX .. "playnext", {
  description = "Queue one track to play next, ahead of the existing queue, without clearing current playback.",
  options = {{ type = 3, name = "search", description = "Track name or URL", required = true }},
}, function(self, interaction)
  if not is_dj(interaction) then return end
  defer(interaction, true)
  local search = opt_value(interaction, "search", "")
  local entries, _playlist, err = search_playables(search)
  if not entries or #entries == 0 then
    return followup(interaction, embed({ description = "Could not resolve that source: " .. tostring(err or "not found"), color = COLOR.red }), true)
  end
  local track = entries[1]
  local requester_id = interaction.member.user.id
  insert_queue_front(interaction.guild_id, track.uri, track.title, requester_id, new_track_uid())
  record_track_queued(interaction.guild_id, track.uri, track.title, requester_id)
  if not player_is_active(interaction.guild_id) then
    local channel_id = resolve_target_channel(interaction)
    if channel_id then copas.addthread(function() process_queue(interaction.guild_id, channel_id) end) end
  end
  followup(interaction, embed({ description = "**Playing next:** " .. track.title, color = COLOR.green }), true)
end)

bot:command(PREFIX .. "skip", {
  description = "Skip the current track and move playback to the next queued item or Auto-DJ recommendation.",
}, function(self, interaction)
  if not is_dj(interaction) then return end
  if player_is_active(interaction.guild_id) then
    bot.lavalink:stop(interaction.guild_id)
    reply(interaction, embed({ description = "⏭️ Skipped", color = COLOR.blurple }), true)
  else
    reply(interaction, embed({ description = "❌ Nothing is playing.", color = COLOR.red }), true)
  end
end)

bot:command(PREFIX .. "stop", {
  description = "Stop playback, clear the queue, remove recovery state, and reset the bot for this server.",
}, function(self, interaction)
  if not is_dj(interaction) then return end
  stop_playback(interaction.guild_id)
  q("DELETE FROM harmonic_active_playlists WHERE guild_id = %s AND bot_name = 'harmonic'", interaction.guild_id)
  reply(interaction, embed({ title = "⏹️ Stopped", description = "Music stopped and cleared.", color = COLOR.red }), true)
end)

bot:command(PREFIX .. "sleep", {
  description = "Stop playback and disconnect after N minutes. Use 0 to cancel an active timer.",
  options = {{ type = 4, name = "minutes", description = "Minutes until playback stops automatically (0 cancels the current timer)", required = true, min_value = 0, max_value = 240 }},
}, function(self, interaction)
  if not is_dj(interaction) then return end
  local guild_id = interaction.guild_id
  local minutes = opt_value(interaction, "minutes", 0)
  local my_token = mono()
  sleep_timers[guild_id] = my_token
  if minutes <= 0 then
    sleep_timers[guild_id] = nil
    return reply(interaction, embed({ description = "⏰ Sleep timer cancelled.", color = COLOR.orange }), true)
  end
  copas.addthread(function()
    copas.sleep(minutes * 60)
    if sleep_timers[guild_id] ~= my_token then return end
    sleep_timers[guild_id] = nil
    stop_playback(guild_id)
    q("DELETE FROM harmonic_active_playlists WHERE guild_id = %s AND bot_name = 'harmonic'", guild_id)
    disconnect_voice(guild_id)
    send_feedback(guild_id, embed({ title = "😴 Sleep Timer", description = "Playback stopped — sleep timer elapsed.", color = COLOR.dark_purple }))
  end)
  reply(interaction, embed({ description = ("😴 Sleep timer set for **%d** minute(s). Playback will stop automatically."):format(minutes), color = COLOR.blue }), true)
end)

bot:command(PREFIX .. "pause", {
  description = "Pause the current track without clearing the queue or playback position.",
}, function(self, interaction)
  if not is_dj(interaction) then return end
  if player_is_active(interaction.guild_id) and not playback_tracking[interaction.guild_id].paused then
    bot.lavalink:set_paused(interaction.guild_id, true)
    sync_pause_state(interaction.guild_id, true)
    reply(interaction, embed({ description = "⏸️ Paused", color = COLOR.blue }), true)
  else
    reply(interaction, embed({ description = "❌ Nothing is currently playing.", color = COLOR.red }), true)
  end
end)

bot:command(PREFIX .. "resume", {
  description = "Resume the paused track from its current playback position.",
}, function(self, interaction)
  if not is_dj(interaction) then return end
  if player_is_active(interaction.guild_id) and playback_tracking[interaction.guild_id].paused then
    bot.lavalink:set_paused(interaction.guild_id, false)
    sync_pause_state(interaction.guild_id, false)
    reply(interaction, embed({ description = "▶️ Resumed", color = COLOR.green }), true)
  else
    reply(interaction, embed({ description = "❌ Nothing is currently paused.", color = COLOR.red }), true)
  end
end)

bot:command(PREFIX .. "clear", {
  description = "Clear the upcoming queue, stop playback, and reset stored playback state for this server.",
}, function(self, interaction)
  if not is_dj(interaction) then return end
  stop_playback(interaction.guild_id)
  q("DELETE FROM harmonic_active_playlists WHERE guild_id = %s AND bot_name = 'harmonic'", interaction.guild_id)
  q("DELETE FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic'", interaction.guild_id)
  q("DELETE FROM harmonic_queue_backup WHERE guild_id = %s AND bot_name = 'harmonic'", interaction.guild_id)
  reply(interaction, embed({ description = "🗑️ Playback stopped and queue cleared.", color = COLOR.red }), true)
end)

bot:command(PREFIX .. "join", {
  description = "Force the bot to join your current voice channel, or its configured home channel if one is saved.",
}, function(self, interaction)
  defer(interaction, true)
  local channel_id = resolve_target_channel(interaction)
  if not channel_id then
    return followup_text(interaction, "Join a channel first, or set a home channel.", true)
  end
  ensure_voice_connection(interaction.guild_id, channel_id)
  followup(interaction, embed({ description = ("Joined <#%s>."):format(channel_id), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "leave", {
  description = "Disconnect the bot from voice and clear any pending recovery handoff for this server.",
}, function(self, interaction)
  if not is_dj(interaction) then return end
  stop_playback(interaction.guild_id)
  q("DELETE FROM harmonic_active_playlists WHERE guild_id = %s AND bot_name = 'harmonic'", interaction.guild_id)
  disconnect_voice(interaction.guild_id)
  reply(interaction, embed({ description = "👋 Left the voice channel.", color = COLOR.blurple }), true)
end)

bot:command(PREFIX .. "nowplaying", {
  description = "Show the current track, progress bar, requester, and live playback status.",
}, function(self, interaction)
  local data = playback_tracking[interaction.guild_id]
  if not data then
    return reply(interaction, embed({ description = "Nothing playing.", color = COLOR.red }), true)
  end
  local pos = current_track_position(interaction.guild_id)
  local e = embed({
    title = "🎵 Now Playing", color = COLOR.blue,
    description = ("**[%s](%s)**\n\n`%s`"):format(data.title or "Playing", data.url, make_progress_bar(pos, data.duration)),
    fields = { field("Filter", data.current_filter or "none", true) },
  })
  if data.requester_id then
    table.insert(e.fields, 1, field("Requested by", resolve_requester_name(interaction.guild_id, data.requester_id), true))
  end
  reply(interaction, e, true)
end)

-- ============================================================================
-- Commands: Queue management
-- ============================================================================

bot:command(PREFIX .. "queue", {
  description = "Show the current queue with paging, requester names, and track positions",
  options = {{ type = 4, name = "page", description = "Page number", required = false, min_value = 1 }},
}, function(self, interaction)
  defer(interaction, true)
  local page = math.max(1, opt_value(interaction, "page", 1))
  local per_page = 10
  local offset = (page - 1) * per_page
  local total = queue_count(interaction.guild_id)
  local rows = q("SELECT title, requester_id FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC LIMIT %s OFFSET %s", interaction.guild_id, per_page, offset) or {}
  if #rows == 0 then
    return followup(interaction, embed({ description = "Queue empty.", color = COLOR.red }), true)
  end
  local lines = {}
  for idx, row in ipairs(rows) do
    table.insert(lines, ("**%d.** %s — *%s*"):format(offset + idx, row.title, resolve_requester_name(interaction.guild_id, row.requester_id)))
  end
  local pages = math.max(1, math.ceil(total / per_page))
  followup(interaction, embed({ title = "📜 Queue", description = table.concat(lines, "\n"), color = COLOR.blurple,
    footer = ("Page %d/%d • %d queued track(s)"):format(page, pages, total) }), true)
end)

bot:command(PREFIX .. "shuffle", {
  description = "Smart-shuffle the upcoming queue while keeping duplicate tracks separated when possible.",
}, function(self, interaction)
  if not is_dj(interaction) then return end
  local n = shuffle_queue_rows(interaction.guild_id, false)
  if n <= 0 then return reply(interaction, embed({ description = "Queue empty.", color = COLOR.red }), true) end
  snapshot_queue_backup(interaction.guild_id)
  reply(interaction, embed({ description = ("🔀 Shuffled %d queued track(s)."):format(n), color = COLOR.green }), true)
end)

local function queue_index_autocomplete_choices(guild_id, current)
  local rows = q("SELECT video_url, title FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC LIMIT 200", guild_id) or {}
  local needle = trim(current):lower()
  local choices = {}
  for position, row in ipairs(rows) do
    local title = row.title or "Unknown title"
    if needle == "" or needle == tostring(position) or title:lower():find(needle, 1, true) then
      table.insert(choices, { name = compact_title(("%d. %s"):format(position, title), 95), value = position })
      if #choices >= 25 then break end
    end
  end
  return choices
end

bot:command(PREFIX .. "remove", {
  description = "Remove a queued track by its queue number so it will not play later.",
  options = {{ type = 4, name = "index", description = "Queue position", required = true, autocomplete = true }},
}, function(self, interaction)
  if not is_dj(interaction) then return end
  local index = opt_value(interaction, "index", 0)
  if index < 1 then return reply_text(interaction, "Invalid index.", true) end
  local row = q1("SELECT id, video_url, title, track_uid FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC LIMIT 1 OFFSET %s", interaction.guild_id, index - 1)
  if not row then return reply_text(interaction, "Invalid index.", true) end
  q("DELETE FROM harmonic_queue WHERE id = %s AND guild_id = %s AND bot_name = 'harmonic'", row.id, interaction.guild_id)
  delete_backup_track(interaction.guild_id, row.track_uid, row.video_url, row.title)
  reply(interaction, embed({ description = "Removed item #" .. index, color = COLOR.green }), true)
end)

bot:command(PREFIX .. "skipto", {
  description = "Drop everything before a chosen queue position and jump playback forward to that track.",
  options = {{ type = 4, name = "index", description = "Queue position", required = true, autocomplete = true }},
}, function(self, interaction)
  if not is_dj(interaction) then return end
  local index = opt_value(interaction, "index", 0)
  if index < 1 then return reply_text(interaction, "Invalid index.", true) end
  defer(interaction, true)
  local skip_n = index - 1
  local rows = q("SELECT id, video_url, title, track_uid FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC LIMIT %s", interaction.guild_id, skip_n) or {}
  for _, r in ipairs(rows) do
    q("DELETE FROM harmonic_queue WHERE id = %s", r.id)
    delete_backup_track(interaction.guild_id, r.track_uid, r.video_url, r.title)
  end
  if player_is_active(interaction.guild_id) then bot.lavalink:stop(interaction.guild_id) end
  followup(interaction, embed({ description = "Skipped to #" .. index, color = COLOR.green }), true)
end)

bot:command(PREFIX .. "move", {
  description = "Move a queued track from one queue slot to another without rebuilding the entire session manually.",
  options = {
    { type = 4, name = "frm", description = "From position", required = true, autocomplete = true },
    { type = 4, name = "to", description = "To position", required = true, autocomplete = true },
  },
}, function(self, interaction)
  if not is_dj(interaction) then return end
  defer(interaction, true)
  local frm, to = opt_value(interaction, "frm", 0), opt_value(interaction, "to", 0)
  local rows = q("SELECT id, video_url, title, requester_id, track_uid FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC", interaction.guild_id) or {}
  if frm > #rows or to > #rows or frm < 1 or to < 1 then
    return followup_text(interaction, "Invalid index", true)
  end
  local item = table.remove(rows, frm)
  table.insert(rows, clamp(to, 1, #rows + 1), item)
  q("DELETE FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic'", interaction.guild_id)
  for _, r in ipairs(rows) do
    q("INSERT INTO harmonic_queue (guild_id, bot_name, video_url, title, requester_id, track_uid) VALUES (%s, 'harmonic', %s, %s, %s, %s)",
      interaction.guild_id, r.video_url, r.title, r.requester_id, r.track_uid)
  end
  snapshot_queue_backup(interaction.guild_id)
  followup(interaction, embed({ description = ("Moved item from %d to %d"):format(frm, to), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "bump", {
  description = "Move a queued track to the front so it plays next",
  options = {{ type = 4, name = "index", description = "Queue position", required = true, autocomplete = true }},
}, function(self, interaction)
  if not is_dj(interaction) then return end
  local index = opt_value(interaction, "index", 0)
  if index < 1 then return reply_text(interaction, "Invalid index.", true) end
  local row = q1("SELECT id, video_url, title, requester_id, track_uid FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC LIMIT 1 OFFSET %s", interaction.guild_id, index - 1)
  if not row then return reply_text(interaction, "Invalid index.", true) end
  q("DELETE FROM harmonic_queue WHERE id = %s AND guild_id = %s AND bot_name = 'harmonic'", row.id, interaction.guild_id)
  insert_queue_front(interaction.guild_id, row.video_url, row.title, row.requester_id, row.track_uid)
  snapshot_queue_backup(interaction.guild_id)
  reply(interaction, embed({ description = "⬆️ Moved **" .. row.title .. "** to play next.", color = COLOR.green }), true)
end)

bot:command(PREFIX .. "clearmine", {
  description = "Remove your own queued songs without touching other listeners' tracks",
}, function(self, interaction)
  defer(interaction, true)
  local requester_id = interaction.member.user.id
  local row = q1("SELECT COUNT(*) AS c FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' AND requester_id = %s", interaction.guild_id, requester_id)
  local removed = row and tonumber(row.c) or 0
  if removed > 0 then
    q("DELETE FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' AND requester_id = %s", interaction.guild_id, requester_id)
    q("DELETE FROM harmonic_queue_backup WHERE guild_id = %s AND bot_name = 'harmonic' AND requester_id = %s", interaction.guild_id, requester_id)
  end
  followup(interaction, embed({ description = ("🧹 Removed **%d** of your queued track(s)."):format(removed), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "voteskip", {
  description = "Start or join a vote skip when no DJ is around to skip directly",
}, function(self, interaction)
  local guild_id = interaction.guild_id
  if not player_is_active(guild_id) then
    return reply_text(interaction, "Nothing is playing right now.", true)
  end
  if is_dj(interaction, true) then
    bot.lavalink:stop(guild_id)
    return reply(interaction, embed({ description = "⏭️ DJ override used: skipped the current track.", color = COLOR.green }), true)
  end
  local channel_id = playback_tracking[guild_id].channel_id
  local listeners = channel_human_listeners(guild_id, channel_id)
  local user_id = interaction.member.user.id
  local in_channel = false
  for _, uid in ipairs(listeners) do if uid == user_id then in_channel = true end end
  if not in_channel then return reply_text(interaction, "Join the same voice channel first.", true) end
  local required = math.max(2, math.floor(#listeners / 2) + 1)
  vote_skip_sessions[guild_id] = vote_skip_sessions[guild_id] or {}
  vote_skip_sessions[guild_id][user_id] = true
  local count = 0
  for _ in pairs(vote_skip_sessions[guild_id]) do count = count + 1 end
  if count >= required then
    vote_skip_sessions[guild_id] = nil
    bot.lavalink:stop(guild_id)
    return reply(interaction, embed({ description = ("⏭️ Vote skip passed with **%d/%d** votes."):format(count, required), color = COLOR.green }))
  end
  reply(interaction, embed({ description = ("🗳️ Vote recorded: **%d/%d** votes to skip."):format(count, required), color = COLOR.blurple }), true)
end)

local function queue_vote(interaction, direction)
  local guild_id, index = interaction.guild_id, opt_value(interaction, "index", 0)
  if not player_is_active(guild_id) then return reply_text(interaction, "Nothing is playing right now.", true) end
  local channel_id = playback_tracking[guild_id].channel_id
  local listeners = channel_human_listeners(guild_id, channel_id)
  local user_id = interaction.member.user.id
  local in_channel = false
  for _, uid in ipairs(listeners) do if uid == user_id then in_channel = true end end
  if not in_channel then return reply_text(interaction, "Join the same voice channel first.", true) end
  if index < 1 then return reply_text(interaction, "Invalid index.", true) end
  local row = q1("SELECT id, video_url, title, requester_id, track_uid FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC LIMIT 1 OFFSET %s", guild_id, index - 1)
  if not row then return reply_text(interaction, "Invalid index.", true) end
  local key = tostring(guild_id) .. ":" .. tostring(row.id)
  local votes = queue_votes[key] or { up = {}, down = {} }
  queue_votes[key] = votes
  local required = math.max(2, math.floor(#listeners / 2) + 1)
  if direction == "up" then
    votes.down[user_id] = nil
    votes.up[user_id] = true
    local n = 0; for _ in pairs(votes.up) do n = n + 1 end
    if n >= required then
      queue_votes[key] = nil
      q("DELETE FROM harmonic_queue WHERE id = %s", row.id)
      insert_queue_front(guild_id, row.video_url, row.title, row.requester_id, row.track_uid)
      snapshot_queue_backup(guild_id)
      return reply(interaction, embed({ description = ("⬆️ **%s** got enough upvotes and will play next!"):format(row.title), color = COLOR.green }))
    end
    reply(interaction, embed({ description = ("🔺 Upvoted **#%d** (%d/%d) to play next."):format(index, n, required), color = COLOR.blurple }), true)
  else
    votes.up[user_id] = nil
    votes.down[user_id] = true
    local n = 0; for _ in pairs(votes.down) do n = n + 1 end
    if n >= required then
      queue_votes[key] = nil
      q("DELETE FROM harmonic_queue WHERE id = %s", row.id)
      delete_backup_track(guild_id, row.track_uid, row.video_url, row.title)
      return reply(interaction, embed({ description = ("⬇️ **%s** got enough downvotes and was removed from the queue."):format(row.title), color = COLOR.orange }))
    end
    reply(interaction, embed({ description = ("🔻 Downvoted **#%d** (%d/%d)."):format(index, n, required), color = COLOR.blurple }), true)
  end
end

bot:command(PREFIX .. "upvote", {
  description = "Upvote a queued track; enough listener upvotes bump it to play next.",
  options = {{ type = 4, name = "index", description = "Queue position", required = true }},
}, function(self, interaction) queue_vote(interaction, "up") end)

bot:command(PREFIX .. "downvote", {
  description = "Downvote a queued track; enough listener downvotes removes it from the queue.",
  options = {{ type = 4, name = "index", description = "Queue position", required = true }},
}, function(self, interaction) queue_vote(interaction, "down") end)

bot:command(PREFIX .. "radio", {
  description = "Queue several tracks matching a mood or vibe, e.g. 'chill lofi' or 'workout hype'.",
  options = {
    { type = 3, name = "mood", description = "Mood or vibe", required = true },
    { type = 4, name = "count", description = "How many tracks (1-10)", required = false, min_value = 1, max_value = 10 },
  },
}, function(self, interaction)
  defer(interaction, false)
  local mood = opt_value(interaction, "mood", "")
  local count = opt_value(interaction, "count", 5)
  local channel_id = invoker_voice_channel(interaction)
  if not channel_id then
    return followup(interaction, embed({ description = "Join a voice channel first.", color = COLOR.red }))
  end
  local entries, _p, err = search_playables(mood:sub(1, 100) .. " mix")
  if not entries or #entries == 0 then
    return followup(interaction, embed({ description = ("Couldn't find tracks for **%s**."):format(mood), color = COLOR.red }))
  end
  local requester_id = interaction.member.user.id
  local n = 0
  for i = 1, math.min(count, #entries) do
    enqueue_track(interaction.guild_id, entries[i].uri, entries[i].title, requester_id, new_track_uid())
    n = n + 1
  end
  if not player_is_active(interaction.guild_id) then
    copas.addthread(function() process_queue(interaction.guild_id, channel_id) end)
  end
  followup(interaction, embed({ title = "📻 Mood Radio", description = ("Queued **%d** track(s) for the vibe: *%s*."):format(n, mood), color = COLOR.green }))
end)

-- ============================================================================
-- Commands: Audio & filters
-- ============================================================================

bot:command(PREFIX .. "volume", {
  description = "Set the playback volume for this server from 1 to 200 percent.",
  options = {{ type = 4, name = "vol", description = "Volume percent", required = true, min_value = 1, max_value = 200 }},
}, function(self, interaction)
  if not is_dj(interaction) then return end
  local vol = clamp(opt_value(interaction, "vol", 100), 1, 200)
  set_guild_setting(interaction.guild_id, "volume", vol)
  if player_is_active(interaction.guild_id) then bot.lavalink:set_volume(interaction.guild_id, vol) end
  reply(interaction, embed({ description = ("🔊 Volume set to %d%%"):format(vol), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "loop", {
  description = "Choose whether playback loops nothing, the current song, or the full queue.",
  options = {{ type = 3, name = "mode", description = "Loop mode", required = true,
    choices = { { name = "Off", value = "off" }, { name = "Song", value = "song" }, { name = "Queue", value = "queue" } } }},
}, function(self, interaction)
  if not is_dj(interaction) then return end
  local mode = opt_value(interaction, "mode", "queue")
  if mode ~= "off" and mode ~= "song" and mode ~= "queue" then return reply_text(interaction, "Invalid mode.", true) end
  set_guild_setting(interaction.guild_id, "loop_mode", mode)
  reply(interaction, embed({ description = "🔁 Looping set to: " .. mode, color = COLOR.green }), true)
end)

bot:command(PREFIX .. "filter", {
  description = "Apply an audio filter such as nightcore, vaporwave, or bass boost to upcoming playback.",
  options = {
    { type = 3, name = "mode", description = "Choose an audio filter to apply", required = true, choices = FILTER_CHOICES },
    { type = 3, name = "stack", description = "Optional second filter to layer on top (e.g. bassboost + nightcore)", required = false, choices = FILTER_CHOICES },
  },
}, function(self, interaction)
  if not is_dj(interaction) then return end
  local mode = opt_value(interaction, "mode")
  local stack = opt_value(interaction, "stack")
  if not FILTER_VALUES[mode] then return reply_text(interaction, "Invalid filter.", true) end
  if stack and not FILTER_VALUES[stack] then return reply_text(interaction, "Invalid stacked filter.", true) end
  defer(interaction, true)
  ensure_guild_settings(interaction.guild_id)
  local stack_value = (stack == nil or stack == "none") and nil or stack
  if stack == nil then
    q("UPDATE harmonic_guild_settings SET filter_mode = %s, custom_speed = 1.0, custom_pitch = 1.0, custom_modifiers_left = 0 WHERE guild_id = %s", mode, interaction.guild_id)
  else
    q("UPDATE harmonic_guild_settings SET filter_mode = %s, filter_stack = %s, custom_speed = 1.0, custom_pitch = 1.0, custom_modifiers_left = 0 WHERE guild_id = %s", mode, stack_value, interaction.guild_id)
  end
  local new_speed = 1.0
  if player_is_active(interaction.guild_id) then
    local filters = {}
    new_speed = apply_filter_preset(filters, mode, 1.0)
    if stack_value and stack_value ~= mode then new_speed = apply_filter_preset(filters, stack_value, new_speed) end
    bot.lavalink:update_player(interaction.guild_id, { filters = filters })
    playback_tracking[interaction.guild_id].speed = new_speed
    playback_tracking[interaction.guild_id].current_filter = mode
  end
  local label = FILTER_LABEL[mode] or mode
  if stack_value and stack_value ~= mode then
    followup(interaction, embed({ description = ("🎛️ Filter set to: **%s** + **%s**."):format(label, FILTER_LABEL[stack_value] or stack_value), color = COLOR.blurple }), true)
  else
    followup(interaction, embed({ description = ("🎛️ Filter set to: **%s**."):format(label), color = COLOR.blurple }), true)
  end
end)

bot:command(PREFIX .. "fade", {
  description = "Customize track fade transitions, let the bot pick smart fade timing, or enable BPM-matched mixing.",
  options = {
    { type = 3, name = "mode", description = "Fade mode", required = true, choices = {
      { name = "Smart Adaptive Fades", value = "smart" }, { name = "Custom Fades", value = "fade" },
      { name = "Beat-Matched Mixing", value = "mix" }, { name = "Disable Fades", value = "off" } } },
    { type = 10, name = "seconds", description = "Fade length in seconds, from 0.5 to 20", required = false },
    { type = 3, name = "curve", description = "Volume curve", required = false, choices = {
      { name = "Linear", value = "linear" }, { name = "Smooth", value = "smooth" },
      { name = "Slow Start", value = "ease_in" }, { name = "Soft Land", value = "ease_out" } } },
  },
}, function(self, interaction)
  if not is_dj(interaction) then return end
  local mode = opt_value(interaction, "mode")
  if mode ~= "off" and mode ~= "fade" and mode ~= "smart" and mode ~= "mix" then return reply_text(interaction, "Invalid fade mode.", true) end
  defer(interaction, true)
  local curve = opt_value(interaction, "curve", "smooth")
  if curve ~= "linear" and curve ~= "smooth" and curve ~= "ease_in" and curve ~= "ease_out" then curve = "smooth" end
  local seconds = clamp(opt_value(interaction, "seconds", 3.0), 0.25, 12.0)
  ensure_guild_settings(interaction.guild_id)
  q("UPDATE harmonic_guild_settings SET transition_mode = %s, fade_seconds = %s, fade_curve = %s WHERE guild_id = %s", mode, seconds, curve, interaction.guild_id)
  local message, color
  if mode == "smart" then
    message, color = "🌊 Smart fades enabled. I will use short, smooth ramps that adapt to track length and active filters.", COLOR.green
  elseif mode == "fade" then
    message, color = ("🌊 Custom fades enabled: %gs using %s."):format(seconds, curve:gsub("_", " ")), COLOR.green
  elseif mode == "mix" then
    message, color = "🎚️ Beat-matched mixing enabled. Transitions use a beat-aligned fade when consecutive tracks share a compatible tempo.", COLOR.green
  else
    message, color = "⏹️ Smooth fades disabled.", COLOR.red
  end
  followup(interaction, embed({ description = message, color = color }), true)
end)

bot:command(PREFIX .. "modify", {
  description = "Apply temporary custom speed and pitch modifiers to the next few tracks in the queue.",
  options = {
    { type = 10, name = "speed", description = "Speed multiplier (0.5 to 2.0)", required = false },
    { type = 10, name = "pitch", description = "Pitch multiplier (0.5 to 2.0)", required = false },
    { type = 4, name = "duration", description = "How many tracks this lasts (default 1)", required = false, min_value = 1 },
  },
}, function(self, interaction)
  if not is_dj(interaction) then return end
  defer(interaction, true)
  ensure_guild_settings(interaction.guild_id)
  local speed = clamp(opt_value(interaction, "speed", 1.0), 0.5, 2.0)
  local pitch = clamp(opt_value(interaction, "pitch", 1.0), 0.5, 2.0)
  local duration = opt_value(interaction, "duration", 1)
  local settings = get_guild_settings(interaction.guild_id)
  if settings.filter_mode and settings.filter_mode ~= "none" then
    return followup(interaction, embed({ description = "❌ **Conflict:** Disable standard Filters via `/harmonic_main_filter none` first.", color = COLOR.red }), true)
  end
  if playback_tracking[interaction.guild_id] then
    playback_tracking[interaction.guild_id].offset = current_track_position(interaction.guild_id)
    playback_tracking[interaction.guild_id].start_time = mono()
    playback_tracking[interaction.guild_id].speed = speed
  end
  q("UPDATE harmonic_guild_settings SET custom_speed = %s, custom_pitch = %s, custom_modifiers_left = %s WHERE guild_id = %s", speed, pitch, duration, interaction.guild_id)
  if player_is_active(interaction.guild_id) then
    bot.lavalink:update_player(interaction.guild_id, { filters = { timescale = { speed = speed, pitch = pitch, rate = 1.0 } } })
  end
  followup(interaction, embed({ title = "🎛️ Audio Modifiers Set", description = ("**Speed:** %sx\n**Pitch:** %sx\n*Active for the next %d track(s).*"):format(speed, pitch, duration), color = COLOR.gold }), true)
end)

local function do_seek(interaction, target_seconds)
  if not is_dj(interaction) then return end
  local guild_id = interaction.guild_id
  if not playback_tracking[guild_id] then return reply_text(interaction, "Nothing playing.", true) end
  target_seconds = math.max(0, target_seconds)
  bot.lavalink:seek(guild_id, math.floor(target_seconds * 1000))
  playback_tracking[guild_id].offset = target_seconds
  playback_tracking[guild_id].start_time = mono()
  reply(interaction, embed({ description = ("⏩ Jumped to `%ds`."):format(math.floor(target_seconds)), color = COLOR.green }), true)
end

bot:command(PREFIX .. "seek", {
  description = "Jump to an exact time in the current track using seconds from the start.",
  options = {{ type = 4, name = "seconds", description = "Seconds from the start", required = true, min_value = 0 }},
}, function(self, interaction) do_seek(interaction, opt_value(interaction, "seconds", 0)) end)

bot:command(PREFIX .. "forward", {
  description = "Jump forward within the current track by the number of seconds you provide.",
  options = {{ type = 4, name = "seconds", description = "Seconds to jump forward", required = true, min_value = 1 }},
}, function(self, interaction)
  local guild_id = interaction.guild_id
  if not playback_tracking[guild_id] then return reply_text(interaction, "Nothing playing.", true) end
  do_seek(interaction, current_track_position(guild_id) + opt_value(interaction, "seconds", 10))
end)

bot:command(PREFIX .. "rewind", {
  description = "Jump backward within the current track by the number of seconds you provide.",
  options = {{ type = 4, name = "seconds", description = "Seconds to jump backward", required = true, min_value = 1 }},
}, function(self, interaction)
  local guild_id = interaction.guild_id
  if not playback_tracking[guild_id] then return reply_text(interaction, "Nothing playing.", true) end
  do_seek(interaction, current_track_position(guild_id) - opt_value(interaction, "seconds", 10))
end)

bot:command(PREFIX .. "replay", {
  description = "Restart the current track from the beginning without changing the queue.",
}, function(self, interaction) do_seek(interaction, 0) end)

-- ============================================================================
-- Commands: Smart Auto-DJ & discovery
-- ============================================================================

bot:command(PREFIX .. "autodj", {
  description = "Enable or disable smarter Auto-DJ recommendations when the queue runs dry",
  options = {{ type = 5, name = "enabled", description = "Enable Auto-DJ", required = true }},
}, function(self, interaction)
  if not is_dj(interaction) then return end
  defer(interaction, true)
  local enabled = opt_value(interaction, "enabled", false)
  set_autodj_enabled(interaction.guild_id, enabled)
  followup(interaction, embed({ description = ("📻 Auto-DJ is now **%s**."):format(enabled and "enabled" or "disabled"), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "recommend", {
  description = "Queue a smart recommendation learned from server taste, playlists, and listener feedback.",
  options = {{ type = 6, name = "member", description = "Base the recommendation on this member's taste", required = false }},
}, function(self, interaction)
  defer(interaction, false)
  local target_id = opt_value(interaction, "member") or interaction.member.user.id
  local channel_id = (playback_tracking[interaction.guild_id] and playback_tracking[interaction.guild_id].channel_id)
    or resolve_target_channel(interaction) or invoker_voice_channel(interaction)
  if not channel_id then
    return followup(interaction, embed({ title = "Source Error", description = "Join a channel first or set a home channel.", color = COLOR.red }))
  end
  local chosen, recommendation = pick_smart_recommendation_track(interaction.guild_id, { target_id })
  if not chosen then
    return followup(interaction, embed({ description = "I could not find a recommendation yet. Play a few tracks or save a playlist first.", color = COLOR.red }))
  end
  enqueue_track(interaction.guild_id, chosen.uri, chosen.title, interaction.member.user.id, new_track_uid())
  record_smart_recommendation(interaction.guild_id, interaction.member.user.id, recommendation, chosen, "slash:" .. tostring(target_id))
  local title = "Smart Recommendation Queued"
  if not player_is_active(interaction.guild_id) then
    copas.addthread(function() process_queue(interaction.guild_id, channel_id) end)
    title = "Smart Recommendation Starting"
  end
  followup(interaction, embed({ title = title, description = ("Added **%s** based on **%s**. Queue size: %d"):format(chosen.title, recommendation.reason or "saved taste", queue_count(interaction.guild_id)), color = COLOR.green }))
end)

bot:command(PREFIX .. "like", {
  description = "Teach Auto-DJ to play more tracks like the current one for you.",
}, function(self, interaction)
  local snapshot = get_current_track_snapshot(interaction.guild_id)
  if not snapshot then return reply_text(interaction, "Nothing is playing right now.", true) end
  record_track_feedback(interaction.guild_id, interaction.member.user.id, snapshot.url, snapshot.title, true)
  if TRACK_FEEDBACK_BROADCAST then
    send_feedback(interaction.guild_id, embed({ title = "👍 Auto-DJ Learned", description = ("Someone liked **%s**."):format(snapshot.title or "this track"), color = COLOR.green }))
  end
  reply(interaction, embed({ description = ("Saved your like for **%s**. Auto-DJ will lean toward similar picks."):format(snapshot.title or "this track"), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "dislike", {
  description = "Teach Auto-DJ to avoid the current track for your future recommendations.",
}, function(self, interaction)
  local snapshot = get_current_track_snapshot(interaction.guild_id)
  if not snapshot then return reply_text(interaction, "Nothing is playing right now.", true) end
  record_track_feedback(interaction.guild_id, interaction.member.user.id, snapshot.url, snapshot.title, false)
  if TRACK_FEEDBACK_BROADCAST then
    send_feedback(interaction.guild_id, embed({ title = "👎 Auto-DJ Learned", description = ("Someone disliked **%s**."):format(snapshot.title or "this track"), color = COLOR.orange }))
  end
  reply(interaction, embed({ description = ("Saved your dislike for **%s**. Auto-DJ will avoid it for you."):format(snapshot.title or "this track"), color = COLOR.orange }), true)
end)

bot:command(PREFIX .. "taste", {
  description = "Show the saved taste profile Auto-DJ has learned for you or another member.",
  options = {{ type = 6, name = "member", description = "Whose taste profile to show", required = false }},
}, function(self, interaction)
  local target_id = opt_value(interaction, "member") or interaction.member.user.id
  local target_name = target_id == interaction.member.user.id and (interaction.member.nick or "you")
    or resolve_requester_name(interaction.guild_id, target_id)
  local rows = q("SELECT title, score, play_count, finish_count, like_count, dislike_count, skip_count FROM harmonic_user_track_affinity WHERE guild_id = %s AND user_id = %s ORDER BY score DESC LIMIT 8", interaction.guild_id, target_id) or {}
  if #rows == 0 then
    return reply_text(interaction, ("No saved taste profile for %s yet."):format(target_name), true)
  end
  local lines, played, finished, liked, disliked, skipped = {}, 0, 0, 0, 0, 0
  for idx, r in ipairs(rows) do
    table.insert(lines, ("**%d.** %s *(score %.1f)*"):format(idx, r.title or "Unknown Track", tonumber(r.score) or 0))
    played = played + (tonumber(r.play_count) or 0)
    finished = finished + (tonumber(r.finish_count) or 0)
    liked = liked + (tonumber(r.like_count) or 0)
    disliked = disliked + (tonumber(r.dislike_count) or 0)
    skipped = skipped + (tonumber(r.skip_count) or 0)
  end
  local e = embed({ title = "HARMONIC Taste Profile: " .. target_name, description = table.concat(lines, "\n"), color = COLOR.blurple,
    fields = { field("Signals", ("plays %d | finishes %d | likes %d | dislikes %d | skips %d"):format(played, finished, liked, disliked, skipped), false) } })
  reply(interaction, e, true)
end)

-- ============================================================================
-- Commands: Personal playlists & history
-- ============================================================================

bot:command(PREFIX .. "playlists", {
  description = "List your saved personal playlists and how many tracks each one contains",
}, function(self, interaction)
  local rows = q("SELECT playlist_name, COUNT(*) AS c FROM harmonic_user_playlists WHERE user_id = %s GROUP BY playlist_name ORDER BY playlist_name ASC", interaction.member.user.id) or {}
  if #rows == 0 then return reply_text(interaction, "You do not have any saved playlists yet.", true) end
  local lines = {}
  for i = 1, math.min(20, #rows) do
    table.insert(lines, ("• **%s** — %s track(s)"):format(rows[i].playlist_name, rows[i].c))
  end
  reply(interaction, embed({ title = "🎼 Your Saved Playlists", description = table.concat(lines, "\n"), color = COLOR.blurple }), true)
end)

bot:command(PREFIX .. "deleteplaylist", {
  description = "Delete one of your saved personal playlists by name",
  options = {{ type = 3, name = "name", description = "Playlist name", required = true }},
}, function(self, interaction)
  local name = opt_value(interaction, "name", "")
  local row = q1("SELECT COUNT(*) AS c FROM harmonic_user_playlists WHERE user_id = %s AND playlist_name = %s", interaction.member.user.id, name)
  local count = row and tonumber(row.c) or 0
  if count == 0 then return reply_text(interaction, "That playlist was not found.", true) end
  q("DELETE FROM harmonic_user_playlists WHERE user_id = %s AND playlist_name = %s", interaction.member.user.id, name)
  reply(interaction, embed({ description = ("🗑️ Deleted **%s** (%d track(s))."):format(name, count), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "savequeue", {
  description = "Save the current queue to one of your personal playlists so you can load it again later.",
  options = {{ type = 3, name = "name", description = "Playlist name", required = true }},
}, function(self, interaction)
  defer(interaction, true)
  local name = opt_value(interaction, "name", "")
  local rows = q("SELECT video_url, title FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC", interaction.guild_id) or {}
  if #rows == 0 then return followup_text(interaction, "Queue is empty!", true) end
  for _, r in ipairs(rows) do
    q("INSERT INTO harmonic_user_playlists (user_id, playlist_name, video_url, title) VALUES (%s, %s, %s, %s)", interaction.member.user.id, name, r.video_url, r.title)
  end
  followup(interaction, embed({ description = ("💾 Saved **%d** tracks to your personal playlist: **%s**"):format(#rows, name), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "loadqueue", {
  description = "Load one of your saved personal playlists into the active queue and start playback if needed.",
  options = {{ type = 3, name = "name", description = "Playlist name", required = true }},
}, function(self, interaction)
  defer(interaction, true)
  local name = opt_value(interaction, "name", "")
  local rows = q("SELECT video_url, title FROM harmonic_user_playlists WHERE user_id = %s AND playlist_name = %s", interaction.member.user.id, name) or {}
  if #rows == 0 then return followup_text(interaction, "Playlist not found or empty.", true) end
  for _, r in ipairs(rows) do
    enqueue_track(interaction.guild_id, r.video_url, r.title, interaction.member.user.id, new_track_uid())
  end
  followup(interaction, embed({ description = ("📂 Loaded **%d** tracks from **%s** into the queue!"):format(#rows, name), color = COLOR.green }), true)
  if not player_is_active(interaction.guild_id) then
    local channel_id = invoker_voice_channel(interaction)
    if channel_id then copas.addthread(function() process_queue(interaction.guild_id, channel_id) end) end
  end
end)

bot:command(PREFIX .. "leaderboard", {
  description = "Show the most played tracks from this server based on stored playback history.",
}, function(self, interaction)
  defer(interaction, true)
  local rows = q("SELECT title, COUNT(*) AS plays FROM harmonic_history WHERE guild_id = %s GROUP BY title ORDER BY plays DESC LIMIT 10", interaction.guild_id) or {}
  if #rows == 0 then return followup_text(interaction, "No play history yet.", true) end
  local lines = {}
  for i, r in ipairs(rows) do table.insert(lines, ("**%d.** %s *(Played %s times)*"):format(i, r.title, r.plays)) end
  followup(interaction, embed({ title = "🏆 Server Top Tracks", description = table.concat(lines, "\n"), color = COLOR.gold }), true)
end)

bot:command(PREFIX .. "history", {
  description = "Show the most recent tracks played in this server from playback history.",
}, function(self, interaction)
  defer(interaction, true)
  local rows = q("SELECT title FROM harmonic_history WHERE guild_id = %s ORDER BY played_at DESC LIMIT 5", interaction.guild_id) or {}
  if #rows == 0 then return followup_text(interaction, "No history.", true) end
  local lines = {}
  for _, r in ipairs(rows) do table.insert(lines, "- " .. r.title) end
  followup(interaction, embed({ title = "📜 History", description = table.concat(lines, "\n"), color = COLOR.blurple }), true)
end)

bot:command(PREFIX .. "userhistory", {
  description = "Show the most recent tracks requested by a specific user in this server.",
  options = {{ type = 6, name = "member", description = "Member", required = true }},
}, function(self, interaction)
  local member_id = opt_value(interaction, "member")
  local member_info = resolved_user(interaction, member_id)
  local rows = q("SELECT title, video_url FROM harmonic_history WHERE guild_id = %s AND requester_id = %s ORDER BY played_at DESC LIMIT 10", interaction.guild_id, member_id) or {}
  if #rows == 0 then
    return reply(interaction, embed({ description = ("📭 %s hasn't queued any songs yet."):format(member_info.display_name), color = COLOR.red }), true)
  end
  local lines = {}
  for i, r in ipairs(rows) do table.insert(lines, ("**%d.** [%s](%s)"):format(i, r.title, r.video_url)) end
  reply(interaction, embed({ title = ("🎧 %s's Play History"):format(member_info.display_name), description = table.concat(lines, "\n"), color = COLOR.blue,
    footer = "Use /harmonic_main_steal <user> <number> to add one to the queue!" }), true)
end)

bot:command(PREFIX .. "steal", {
  description = "Copy a track from a member's request history and add it back into the queue.",
  options = {
    { type = 6, name = "member", description = "Member", required = true },
    { type = 4, name = "track_number", description = "Their history position", required = true, min_value = 1 },
  },
}, function(self, interaction)
  local member_id = opt_value(interaction, "member")
  local member_info = resolved_user(interaction, member_id)
  local track_number = opt_value(interaction, "track_number", 1)
  local song = q1("SELECT video_url, title FROM harmonic_history WHERE guild_id = %s AND requester_id = %s ORDER BY played_at DESC LIMIT 1 OFFSET %s", interaction.guild_id, member_id, track_number - 1)
  if not song then
    return reply(interaction, embed({ description = ("❌ Could not find track #%d in their history."):format(track_number), color = COLOR.red }), true)
  end
  enqueue_track(interaction.guild_id, song.video_url, song.title, interaction.member.user.id, new_track_uid())
  reply(interaction, embed({ title = "🥷 Song Stolen!", description = ("Added **%s** to the queue from %s's history."):format(song.title, member_info.display_name), color = COLOR.green }))
  if not player_is_active(interaction.guild_id) then
    local channel_id = invoker_voice_channel(interaction)
    if channel_id then copas.addthread(function() process_queue(interaction.guild_id, channel_id) end) end
  end
end)

bot:command(PREFIX .. "grab", {
  description = "Send yourself the currently playing track in a direct message for easy saving or sharing.",
}, function(self, interaction)
  defer(interaction, true)
  local data = playback_tracking[interaction.guild_id]
  if not data then return followup(interaction, embed({ description = "Nothing is currently playing.", color = COLOR.red }), true) end
  local user_id = interaction.member.user.id
  local display_name = interaction.member.nick or (interaction.member.user and interaction.member.user.username) or "there"
  local dm_channel, err = bot.rest:post("/users/@me/channels", { recipient_id = user_id })
  if not dm_channel then
    return followup(interaction, embed({ description = "❌ I can't DM you! Please check your privacy settings.", color = COLOR.red }), true)
  end
  bot.rest:post(("/channels/%s/messages"):format(dm_channel.id), { embeds = { embed({
    title = "🎵 Track Saved!",
    description = ("Hey **%s**!\nHere is the track you wanted to save:\n\n**[%s](%s)**"):format(display_name, data.title or "Unknown Title", data.url),
    color = 0x5865F2,
  }) } })
  followup(interaction, embed({ description = "📬 Check your DMs!", color = COLOR.green }), true)
end)

-- ============================================================================
-- Commands: Utility
-- ============================================================================

bot:command(PREFIX .. "ping", {
  description = "Show the bot websocket latency so you can quickly check responsiveness.",
}, function(self, interaction)
  reply(interaction, embed({ description = "🏓 Pong!", color = COLOR.green }), true)
end)

bot:command(PREFIX .. "uptime", {
  description = "Show how long this bot process has been running since its last startup.",
}, function(self, interaction)
  local secs = os.time() - bot.start_time
  local h, m, s = math.floor(secs / 3600), math.floor((secs % 3600) / 60), secs % 60
  reply(interaction, embed({ description = ("⏱️ Uptime: %d:%02d:%02d"):format(h, m, s), color = COLOR.green }), true)
end)

bot:command(PREFIX .. "stats", {
  description = "Show quick bot statistics such as guild count and active player count.",
}, function(self, interaction)
  local active = 0
  for _ in pairs(playback_tracking) do active = active + 1 end
  reply(interaction, embed({ title = "📊 Harmonic Stats", color = COLOR.blurple, fields = {
    field("Active Players", active, true),
    field("Lavalink Session", bot.lavalink.session_id and "connected" or "connecting", true),
  }}), true)
end)

bot:command(PREFIX .. "help", {
  description = "Show a categorized help menu for all HARMONIC music commands and utilities",
}, function(self, interaction)
  local names = {}
  for name in pairs(bot.commands) do table.insert(names, name) end
  table.sort(names)
  reply(interaction, embed({ title = "📚 Command List", description = table.concat(names, ", "), color = COLOR.blue }), true)
end)

bot:command(PREFIX .. "lyrics", {
  description = "Show lyrics for the currently playing track, synced to the current position when available.",
}, function(self, interaction)
  local data = playback_tracking[interaction.guild_id]
  if not data then return reply(interaction, embed({ description = "Nothing is playing.", color = COLOR.red }), true) end
  defer(interaction, false)
  local title = data.title or "Unknown"
  local result = fetch_lyrics(title)
  if not result or (not result.plain and not result.synced_raw) then
    return followup(interaction, embed({ description = ("No lyrics found for **%s**."):format(title), color = COLOR.red }))
  end
  local e = embed({ title = "📜 " .. (result.track_name or title), color = COLOR.blue })
  if result.artist_name then e.author = { name = result.artist_name } end
  if result.synced_raw then
    local synced = parse_synced_lyrics(result.synced_raw)
    local pos = current_track_position(interaction.guild_id)
    local current_idx = 1
    for idx, line in ipairs(synced) do
      if line.ts <= pos then current_idx = idx else break end
    end
    local body = {}
    for idx = math.max(1, current_idx - 2), math.min(#synced, current_idx + 4) do
      local text = synced[idx].text
      table.insert(body, idx == current_idx and ("**" .. text .. "**") or text)
    end
    e.description = table.concat(body, "\n"):sub(1, 4000)
    e.footer = { text = "Synced to current playback position — rerun to refresh." }
  else
    e.description = (result.plain or "No lyrics text available."):sub(1, 4000)
  end
  followup(interaction, e)
end)

-- ============================================================================
-- Command: Panel (interactive control panel with message-component buttons)
-- ============================================================================

local function build_panel_embed(guild_id)
  local s = get_guild_settings(guild_id)
  local vol, loop_mode = s.volume or 100, s.loop_mode or "queue"
  local e = embed({ title = "🎛️ HARMONIC Music Control Panel", color = COLOR.grey })
  local data = playback_tracking[guild_id]
  if data then
    local pos = current_track_position(guild_id)
    local bar = make_progress_bar(pos, data.duration)
    local now_playing = data.url and ("**[%s](%s)**"):format(data.title or "Playing", data.url) or ("**%s**"):format(data.title or "Playing")
    e.fields = { field("Now Playing", now_playing .. "\n`" .. bar .. "`", false) }
    if data.requester_id then table.insert(e.fields, field("Requested by", resolve_requester_name(guild_id, data.requester_id), true)) end
    table.insert(e.fields, field("Filter", data.current_filter or "none", true))
  else
    e.description = "Nothing is playing right now."
    e.fields = {}
  end
  table.insert(e.fields, field("Volume", vol .. "%", true))
  table.insert(e.fields, field("Loop", loop_mode, true))
  e.footer = { text = "HARMONIC Main Music System" }
  return e
end

local PANEL_ROW1 = { type = 1, components = {
  { type = 2, style = 1, label = "⏯️ Play/Pause", custom_id = "harmonic_panel_playpause" },
  { type = 2, style = 4, label = "⏹️ Stop", custom_id = "harmonic_panel_stop" },
  { type = 2, style = 2, label = "⏭️ Skip", custom_id = "harmonic_panel_skip" },
}}
local PANEL_ROW2 = { type = 1, components = {
  { type = 2, style = 2, label = "⏪ -10s", custom_id = "harmonic_panel_rw" },
  { type = 2, style = 2, label = "⏩ +10s", custom_id = "harmonic_panel_fw" },
  { type = 2, style = 2, label = "🔉 Vol-", custom_id = "harmonic_panel_voldown" },
  { type = 2, style = 2, label = "🔊 Vol+", custom_id = "harmonic_panel_volup" },
}}
local PANEL_ROW3 = { type = 1, components = {
  { type = 2, style = 2, label = "🔁 Loop", custom_id = "harmonic_panel_loop" },
  { type = 2, style = 3, label = "🔀 Shuffle", custom_id = "harmonic_panel_shuffle" },
  { type = 2, style = 2, label = "📜 View Queue", custom_id = "harmonic_panel_viewqueue" },
}}
local PANEL_COMPONENTS = { PANEL_ROW1, PANEL_ROW2, PANEL_ROW3 }

bot:command(PREFIX .. "panel", {
  description = "Post an interactive control panel with playback, queue, and transport buttons.",
}, function(self, interaction)
  interaction_ack(interaction, 4, { embeds = { build_panel_embed(interaction.guild_id) }, components = PANEL_COMPONENTS })
end)

local function panel_adjust_volume(interaction, delta)
  local s = get_guild_settings(interaction.guild_id)
  local vol = clamp((s.volume or 100) + delta, 1, 200)
  set_guild_setting(interaction.guild_id, "volume", vol)
  if player_is_active(interaction.guild_id) then bot.lavalink:set_volume(interaction.guild_id, vol) end
end

local PANEL_HANDLERS = {
  harmonic_panel_playpause = function(interaction)
    if not is_dj(interaction, true) then return reply_text(interaction, "DJ permission required.", true) end
    local guild_id = interaction.guild_id
    if not player_is_active(guild_id) then return reply_text(interaction, "Nothing is playing.", true) end
    local paused = playback_tracking[guild_id].paused
    bot.lavalink:set_paused(guild_id, not paused)
    sync_pause_state(guild_id, not paused)
    update_message(interaction, build_panel_embed(guild_id), PANEL_COMPONENTS)
  end,
  harmonic_panel_stop = function(interaction)
    if not is_dj(interaction, true) then return reply_text(interaction, "DJ permission required.", true) end
    stop_playback(interaction.guild_id)
    update_message(interaction, build_panel_embed(interaction.guild_id), PANEL_COMPONENTS)
  end,
  harmonic_panel_skip = function(interaction)
    if not is_dj(interaction, true) then return reply_text(interaction, "DJ permission required.", true) end
    if player_is_active(interaction.guild_id) then bot.lavalink:stop(interaction.guild_id) end
    reply_text(interaction, "⏭️ Skipped to next track", true)
  end,
  harmonic_panel_rw = function(interaction)
    if not is_dj(interaction, true) then return reply_text(interaction, "DJ permission required.", true) end
    local guild_id = interaction.guild_id
    if not playback_tracking[guild_id] then return reply_text(interaction, "Nothing playing.", true) end
    local new_pos = math.max(0, current_track_position(guild_id) - 10)
    bot.lavalink:seek(guild_id, new_pos * 1000)
    playback_tracking[guild_id].offset, playback_tracking[guild_id].start_time = new_pos, mono()
    update_message(interaction, build_panel_embed(guild_id), PANEL_COMPONENTS)
  end,
  harmonic_panel_fw = function(interaction)
    if not is_dj(interaction, true) then return reply_text(interaction, "DJ permission required.", true) end
    local guild_id = interaction.guild_id
    if not playback_tracking[guild_id] then return reply_text(interaction, "Nothing playing.", true) end
    local new_pos = current_track_position(guild_id) + 10
    bot.lavalink:seek(guild_id, new_pos * 1000)
    playback_tracking[guild_id].offset, playback_tracking[guild_id].start_time = new_pos, mono()
    update_message(interaction, build_panel_embed(guild_id), PANEL_COMPONENTS)
  end,
  harmonic_panel_voldown = function(interaction)
    if not is_dj(interaction, true) then return reply_text(interaction, "DJ permission required.", true) end
    panel_adjust_volume(interaction, -10)
    update_message(interaction, build_panel_embed(interaction.guild_id), PANEL_COMPONENTS)
  end,
  harmonic_panel_volup = function(interaction)
    if not is_dj(interaction, true) then return reply_text(interaction, "DJ permission required.", true) end
    panel_adjust_volume(interaction, 10)
    update_message(interaction, build_panel_embed(interaction.guild_id), PANEL_COMPONENTS)
  end,
  harmonic_panel_loop = function(interaction)
    if not is_dj(interaction, true) then return reply_text(interaction, "DJ permission required.", true) end
    local s = get_guild_settings(interaction.guild_id)
    local next_mode = ({ off = "queue", queue = "song", song = "off" })[s.loop_mode or "queue"] or "queue"
    set_guild_setting(interaction.guild_id, "loop_mode", next_mode)
    update_message(interaction, build_panel_embed(interaction.guild_id), PANEL_COMPONENTS)
  end,
  harmonic_panel_shuffle = function(interaction)
    if not is_dj(interaction, true) then return reply_text(interaction, "DJ permission required.", true) end
    defer(interaction, true)
    local n = shuffle_queue_rows(interaction.guild_id, false)
    if n <= 0 then return followup_text(interaction, "Queue empty.", true) end
    snapshot_queue_backup(interaction.guild_id)
    followup_text(interaction, "🔀 Queue successfully shuffled!", true)
  end,
  harmonic_panel_viewqueue = function(interaction)
    defer(interaction, true)
    local rows = q("SELECT title FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC LIMIT 10", interaction.guild_id) or {}
    if #rows == 0 then return followup_text(interaction, "Queue is empty.", true) end
    local lines = {}
    for i, r in ipairs(rows) do table.insert(lines, i .. ". " .. r.title) end
    followup_text(interaction, "**Current Queue:**\n" .. table.concat(lines, "\n"), true)
  end,
}

-- ============================================================================
-- Autocomplete + message-component interaction routing
-- (bot.lua's built-in INTERACTION_CREATE handler only reacts to type 2
-- APPLICATION_COMMAND; Gateway supports multiple handlers per event, so this
-- adds a second one covering type 3 MESSAGE_COMPONENT and type 4
-- APPLICATION_COMMAND_AUTOCOMPLETE without touching the shared library.)
-- ============================================================================

local function youtube_search_suggestions(query)
  query = trim(query)
  if #query < 2 or is_explicit_lavalink_query(query) then return {} end
  local response_body = {}
  local ok = https.request({
    url = "https://suggestqueries.google.com/complete/search?client=firefox&ds=yt&q=" .. query:gsub(" ", "%%20"),
    method = "GET",
    sink = ltn12.sink.table(response_body),
  })
  if not ok then return {} end
  local ok2, data = pcall(cjson.decode, table.concat(response_body))
  if not ok2 or type(data) ~= "table" or not data[2] then return {} end
  local out = {}
  for _, s in ipairs(data[2]) do
    if #out >= 10 then break end
    if trim(s) ~= "" then table.insert(out, tostring(s)) end
  end
  return out
end

bot.gateway:on("INTERACTION_CREATE", function(interaction)
  if interaction.type == 4 then
    -- Autocomplete
    local name = interaction.data and interaction.data.name
    local focused
    for _, o in ipairs(interaction.data.options or {}) do
      if o.focused then focused = o end
    end
    if not focused then return autocomplete_reply(interaction, {}) end
    if name == PREFIX .. "play" and focused.name == "search" then
      local current = tostring(focused.value or "")
      local suggestions = youtube_search_suggestions(current)
      if #suggestions == 0 and trim(current) ~= "" then suggestions = { current } end
      local choices = {}
      for _, s in ipairs(suggestions) do
        table.insert(choices, { name = s:sub(1, 100), value = s:sub(1, 100) })
      end
      return autocomplete_reply(interaction, choices)
    end
    if focused.name == "index" or focused.name == "frm" or focused.name == "to" then
      return autocomplete_reply(interaction, queue_index_autocomplete_choices(interaction.guild_id, tostring(focused.value or "")))
    end
    return autocomplete_reply(interaction, {})
  elseif interaction.type == 3 then
    -- Message component (panel buttons)
    local custom_id = interaction.data and interaction.data.custom_id
    local handler = custom_id and PANEL_HANDLERS[custom_id]
    if handler then
      local ok, err = pcall(handler, interaction)
      if not ok then
        print("[harmonic] panel handler error: " .. tostring(err))
        report_error(interaction.guild_id, "command_error", "panel:" .. tostring(custom_id), tostring(err))
      end
    end
  end
end)

-- Auto-disconnect when the last human listener leaves a channel Harmonic is
-- connected to (unless 24/7 mode is on for that guild).
bot.gateway:on("VOICE_STATE_UPDATE", function(d)
  if d.user_id == bot.user_id then return end
  local data = playback_tracking[d.guild_id]
  local channel_id = (data and data.channel_id) or (guild_states[d.guild_id] and guild_states[d.guild_id].voice_channel_id)
  if not channel_id then return end
  copas.addthread(function()
    copas.sleep(0.2) -- let the voice-state cache above finish updating first
    local settings = get_guild_settings(d.guild_id)
    if should_auto_disconnect(d.guild_id, channel_id, settings.stay_in_vc) then
      disconnect_voice(d.guild_id)
      playback_tracking[d.guild_id] = nil
      guild_states[d.guild_id] = nil
    end
  end)
end)

-- ============================================================================
-- Background maintenance loops
-- ============================================================================

local METRICS_HEARTBEAT_INTERVAL = tonumber(env("HARMONIC_METRICS_HEARTBEAT_INTERVAL", "20"))
local POSITION_PERSIST_INTERVAL = tonumber(env("HARMONIC_POSITION_PERSIST_INTERVAL", "10"))
local DIRECT_ORDER_POLL_INTERVAL = tonumber(env("HARMONIC_DIRECT_ORDER_POLL_INTERVAL_SECONDS", "5"))
local DATABASE_JANITOR_INTERVAL = tonumber(env("HARMONIC_DATABASE_JANITOR_INTERVAL_SECONDS", tostring(24 * 3600)))
local QUEUE_SHUFFLE_MAINTENANCE_INTERVAL = tonumber(env("HARMONIC_QUEUE_SHUFFLE_MAINTENANCE_INTERVAL_SECONDS", tostring(30 * 60)))

-- Direct SQL port of harmonic.py's database_janitor_loop (24h): prunes old
-- history/recommendation/error rows and stale, rarely-touched intelligence
-- rows so these tables don't grow unbounded over the bot's lifetime. The
-- harmonic_track_embeddings orphan-cleanup step is skipped -- that table is
-- unused in this stack (no embedding-similarity layer; see the Smart Auto-DJ
-- simplification note near the bottom of this file).
local function run_database_janitor()
  q("DELETE FROM harmonic_history WHERE played_at < NOW() - INTERVAL '30 days'")
  q("DELETE FROM harmonic_smart_recommendations WHERE created_at < NOW() - INTERVAL '90 days'")
  q("DELETE FROM harmonic_error_events WHERE created_at < NOW() - INTERVAL '30 days'")
  q("DELETE FROM harmonic_track_intelligence WHERE last_played < NOW() - INTERVAL '365 days' AND play_count <= 1 AND finish_count = 0")
  q("DELETE FROM harmonic_user_track_affinity WHERE last_requested < NOW() - INTERVAL '365 days' AND play_count <= 1")
  q("DELETE FROM harmonic_track_cooccurrence WHERE updated_at < NOW() - INTERVAL '180 days'")
end

-- Direct port of harmonic.py's queue_shuffle_maintenance_loop (30 min):
-- periodically reshuffles the upcoming queue (keeping the current "up next"
-- slot pinned) for guilds that are actively playing to a channel with real
-- listeners and are in loop_mode == 'queue', so the same running order
-- doesn't go stale over a long session.
local function run_queue_shuffle_maintenance()
  for guild_id, data in pairs(playback_tracking) do
    if data.channel_id and #channel_human_listeners(guild_id, data.channel_id) > 0 then
      local settings = get_guild_settings(guild_id)
      if (settings.loop_mode or "queue") == "queue" then
        local n = shuffle_queue_rows(guild_id, true)
        if n > 1 then snapshot_queue_backup(guild_id) end
      end
    end
  end
end

-- swarm_health + per-guild harmonic_metrics: what Aria/SwarmPanel poll for
-- fleet visibility (queue depth, playback state, recovery flags, heartbeat age).
local function metrics_heartbeat()
  q([[
    INSERT INTO swarm_health (bot_name, last_pulse, status) VALUES ('harmonic', NOW(), 'online')
    ON CONFLICT (bot_name) DO UPDATE SET last_pulse = NOW(), status = 'online'
  ]])
  for guild_id, data in pairs(playback_tracking) do
    local paused = data.paused or false
    q([[
      INSERT INTO harmonic_metrics (guild_id, bot_name, voice_connected, connected_channel_id, player_connected,
        player_playing, player_paused, queue_count, backup_queue_count, is_playing_db, is_paused_db,
        position_seconds, recovery_pending, heartbeat_age_seconds, lavalink_ready, duration_seconds, updated_at)
      VALUES (%s, 'harmonic', TRUE, %s, TRUE, %s, %s, %s, %s, TRUE, %s, %s, FALSE, 0, %s, %s, NOW())
      ON CONFLICT (guild_id, bot_name) DO UPDATE SET
        voice_connected = EXCLUDED.voice_connected, connected_channel_id = EXCLUDED.connected_channel_id,
        player_connected = EXCLUDED.player_connected, player_playing = EXCLUDED.player_playing,
        player_paused = EXCLUDED.player_paused, queue_count = EXCLUDED.queue_count,
        backup_queue_count = EXCLUDED.backup_queue_count, is_playing_db = EXCLUDED.is_playing_db,
        is_paused_db = EXCLUDED.is_paused_db, position_seconds = EXCLUDED.position_seconds,
        lavalink_ready = EXCLUDED.lavalink_ready, duration_seconds = EXCLUDED.duration_seconds, updated_at = NOW()
    ]], guild_id, data.channel_id, not paused, paused, queue_count(guild_id), backup_count(guild_id),
       paused, current_track_position(guild_id), bot.lavalink.session_id ~= nil, math.floor(data.duration or 0))
  end
end

-- Live position checkpointing so a restart resumes close to where playback
-- actually was (harmonic_playback_state.position_seconds / last_checkpoint_at).
local function persist_positions()
  for guild_id, data in pairs(playback_tracking) do
    persist_playback_state(guild_id, data.channel_id, data.url, data.title, current_track_position(guild_id), not data.paused, data.paused, data.track_uid)
  end
end

-- Aria direct-order integration: Aria (the fleet supervisor) drops rows into
-- harmonic_swarm_direct_orders for this bot to execute (join/play/skip/stop/
-- pause/resume/volume/shuffle/clear). Polled, claimed, and cleared here.
local function handle_direct_order(order)
  local guild_id = order.guild_id
  local cmd = order.command
  local ok, err = pcall(function()
    if cmd == "join" and order.vc_id then
      ensure_voice_connection(guild_id, order.vc_id)
    elseif cmd == "leave" then
      stop_playback(guild_id); disconnect_voice(guild_id)
    elseif cmd == "play" and order.data and order.vc_id then
      local entries = search_playables(order.data)
      if entries[1] then
        enqueue_track(guild_id, entries[1].uri, entries[1].title, nil, new_track_uid())
        if not player_is_active(guild_id) then process_queue(guild_id, order.vc_id) end
      end
    elseif cmd == "skip" then
      if player_is_active(guild_id) then bot.lavalink:stop(guild_id) end
    elseif cmd == "stop" then
      stop_playback(guild_id)
    elseif cmd == "pause" then
      bot.lavalink:set_paused(guild_id, true); sync_pause_state(guild_id, true)
    elseif cmd == "resume" then
      bot.lavalink:set_paused(guild_id, false); sync_pause_state(guild_id, false)
    elseif cmd == "volume" and order.data then
      local vol = clamp(tonumber(order.data) or 100, 1, 200)
      set_guild_setting(guild_id, "volume", vol)
      if player_is_active(guild_id) then bot.lavalink:set_volume(guild_id, vol) end
    elseif cmd == "shuffle" then
      shuffle_queue_rows(guild_id, false); snapshot_queue_backup(guild_id)
    elseif cmd == "clear" then
      q("DELETE FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic'", guild_id)
      q("DELETE FROM harmonic_queue_backup WHERE guild_id = %s AND bot_name = 'harmonic'", guild_id)
    end
  end)
  if not ok then
    q("UPDATE harmonic_swarm_direct_orders SET attempts = attempts + 1, last_error = %s WHERE id = %s", tostring(err):sub(1, 500), order.id)
  else
    q("DELETE FROM harmonic_swarm_direct_orders WHERE id = %s", order.id)
  end
end

local function poll_direct_orders()
  local rows = q("SELECT id, guild_id, vc_id, text_channel_id, command, data FROM harmonic_swarm_direct_orders WHERE bot_name = 'harmonic' AND claimed_at IS NULL ORDER BY id ASC LIMIT 5") or {}
  for _, order in ipairs(rows) do
    q("UPDATE harmonic_swarm_direct_orders SET claimed_at = NOW() WHERE id = %s", order.id)
    handle_direct_order(order)
  end
end

-- Rejoin+resume any guild that had a live track when the process last stopped.
local function restore_persistent_state()
  local rows = q("SELECT guild_id, channel_id, video_url, title, position_seconds, track_uid FROM harmonic_playback_state WHERE bot_name = 'harmonic' AND is_playing = TRUE AND channel_id IS NOT NULL") or {}
  for _, row in ipairs(rows) do
    local guild_id, channel_id = row.guild_id, row.channel_id
    copas.addthread(function()
      copas.sleep(2) -- give the gateway a moment to finish READY/voice bookkeeping
      print(("[harmonic] Restoring guild %s playback in channel %s"):format(tostring(guild_id), tostring(channel_id)))
      process_queue(guild_id, channel_id, tonumber(row.position_seconds) or 0)
    end)
  end
end

local function start_background_loops()
  copas.addthread(function()
    while true do
      local ok, err = pcall(metrics_heartbeat)
      if not ok then
        print("[harmonic] metrics_heartbeat error: " .. tostring(err))
        report_error(nil, "runtime", "metrics_heartbeat error", tostring(err))
      end
      copas.sleep(METRICS_HEARTBEAT_INTERVAL)
    end
  end)
  copas.addthread(function()
    while true do
      local ok, err = pcall(persist_positions)
      if not ok then
        print("[harmonic] persist_positions error: " .. tostring(err))
        report_error(nil, "runtime", "persist_positions error", tostring(err))
      end
      copas.sleep(POSITION_PERSIST_INTERVAL)
    end
  end)
  copas.addthread(function()
    while true do
      local ok, err = pcall(poll_direct_orders)
      if not ok then
        print("[harmonic] poll_direct_orders error: " .. tostring(err))
        report_error(nil, "runtime", "poll_direct_orders error", tostring(err))
      end
      copas.sleep(DIRECT_ORDER_POLL_INTERVAL)
    end
  end)
  copas.addthread(function()
    copas.sleep(30 * 60) -- match the Python original's before_loop 30-minute initial delay
    while true do
      local ok, err = pcall(run_queue_shuffle_maintenance)
      if not ok then
        print("[harmonic] queue_shuffle_maintenance error: " .. tostring(err))
        report_error(nil, "runtime", "queue_shuffle_maintenance error", tostring(err))
      end
      copas.sleep(QUEUE_SHUFFLE_MAINTENANCE_INTERVAL)
    end
  end)
  copas.addthread(function()
    while true do
      local ok, err = pcall(run_database_janitor)
      if not ok then
        print("[harmonic] database_janitor error: " .. tostring(err))
        report_error(nil, "runtime", "database_janitor error", tostring(err))
      end
      copas.sleep(DATABASE_JANITOR_INTERVAL)
    end
  end)
end

-- ============================================================================
-- Boot
-- ============================================================================

bot.gateway:on("READY", function(d)
  print("[harmonic] READY -- Harmonic is online.")
  start_background_loops()
  copas.addthread(function()
    -- Wait for the Lavalink websocket to actually be connected before
    -- touching the queue -- process_queue deletes each row before resolving
    -- it, so racing this against Lavalink's own (often slow, cold-start)
    -- connect meant every "no response from Lavalink" failure permanently
    -- destroyed that queued track instead of just skipping playback.
    local waited = 0
    while not (bot.lavalink and bot.lavalink.session_id) and waited < 60 do
      copas.sleep(1)
      waited = waited + 1
    end
    local ok, err = pcall(restore_persistent_state)
    if not ok then
      print("[harmonic] restore_persistent_state error: " .. tostring(err))
      report_error(nil, "runtime", "restore_persistent_state error", tostring(err))
    end
  end)
end)

--[[
  Known simplifications vs. harmonic.py (see final report for full detail):
  - No local yt-dlp audio cache / BPM (aubio) / loudness analysis -- Lavalink's
    own source plugins resolve and stream tracks directly; "best available
    audio quality" is Lavalink's job in this architecture, not a local
    download+transcode step. Beat-matched /fade mix mode falls back to a
    fixed short crossfade rather than measured-BPM beat alignment.
  - No YouTube Data API playlist expansion -- playlist URLs are handed to
    Lavalink's own loadtracks (lavasrc/youtube plugin), which expands them
    server-side; no separate quota-tracked API path.
  - No distributed claim-token/backoff recovery machinery -- this is a single
    bot process per node (as before), so the simpler in-memory
    processing_guild guard is sufficient; the elaborate multi-attempt backoff
    ladders in the Python version existed to survive that same single
    process's own transient Lavalink/voice hiccups, which the leaner retry
    here (search-fail -> short sleep -> retry next queue item) still covers.
  - Smart Auto-DJ recommendation scoring is a faithful SQL port of
    build_smart_recommendation's weighting formula, minus the cross-track
    embedding-similarity layer (no vector embedding service in this stack).
  - harmonic.py's zombie_reaper_loop (5-minute poll of every connected guild's
    voice client for an empty channel) is not a separate loop here -- the
    VOICE_STATE_UPDATE handler above already reacts immediately (after a
    0.2s debounce) whenever the last human listener leaves a channel this
    bot is connected to, which is a strict improvement (event-driven instead
    of up-to-5-minutes-stale) over the same behavior.
  - harmonic.py's cache_cleanup_loop (10-hourly local yt-dlp/pre-cache
    directory cleanup) is not ported: there is no local audio cache in this
    architecture (see the yt-dlp note above) so there is nothing to clean.
  - database_janitor_loop (run_database_janitor, 24h) and
    queue_shuffle_maintenance_loop (run_queue_shuffle_maintenance, 30min) ARE
    ported as direct SQL/logic translations, including harmonic_error_events
    retention -- see the "Error events" section above, which also ports
    harmonic.py's _persist_error_event()/send_error_webhook_log() pair
    (bot.on_error wired via lib/swarmlua/bot.lua's additive hook, same
    pattern as gws.lua).
]]

if env("HARMONIC_DRY_RUN") == "test" then
  -- Exposes internals for the DB/logic smoke test (scripts/db_smoke_test.lua);
  -- not reached in normal operation (that script sets this env var itself).
  return {
    q = q, q1 = q1, ensure_guild_settings = ensure_guild_settings, get_guild_settings = get_guild_settings,
    set_guild_setting = set_guild_setting, enqueue_track = enqueue_track, insert_queue_front = insert_queue_front,
    snapshot_queue_backup = snapshot_queue_backup, delete_backup_track = delete_backup_track,
    shuffle_queue_rows = shuffle_queue_rows, restore_queue_from_backup = restore_queue_from_backup,
    record_track_queued = record_track_queued, record_track_play_started = record_track_play_started,
    record_track_cooccurrence = record_track_cooccurrence, record_track_outcome = record_track_outcome,
    record_track_feedback = record_track_feedback, build_smart_recommendation = build_smart_recommendation,
    load_smart_avoid_keys = load_smart_avoid_keys, get_autodj_enabled = get_autodj_enabled,
    set_autodj_enabled = set_autodj_enabled, persist_playback_state = persist_playback_state,
    clear_playback_state = clear_playback_state, queue_count = queue_count, backup_count = backup_count,
    track_key = track_key, new_track_uid = new_track_uid, bot = bot,
    report_error = report_error, persist_error_event = persist_error_event,
    run_database_janitor = run_database_janitor, run_queue_shuffle_maintenance = run_queue_shuffle_maintenance,
  }
elseif env("HARMONIC_DRY_RUN") then
  print(("[harmonic] dry run OK: %d commands registered, db/lavalink/gateway objects constructed."):format((function()
    local n = 0; for _ in pairs(bot.commands) do n = n + 1 end; return n
  end)()))
  os.exit(0)
end

bot:run()
