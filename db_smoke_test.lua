package.path = "./lib/?.lua;./lib/?/init.lua;" .. package.path

local H = dofile("harmonic.lua")

local TEST_GUILD = "999900001"
local TEST_USER = "999900002"
local TEST_USER2 = "999900003"

local function check(label, ok, err)
  if ok then
    print("OK   " .. label)
  else
    print("FAIL " .. label .. " -> " .. tostring(err))
  end
end

-- guild settings upsert/read/write
H.ensure_guild_settings(TEST_GUILD)
local settings = H.get_guild_settings(TEST_GUILD)
check("get_guild_settings returns row", settings ~= nil and settings.guild_id ~= nil)
H.set_guild_setting(TEST_GUILD, "volume", 77)
H.set_guild_setting(TEST_GUILD, "loop_mode", "song")
H.set_guild_setting(TEST_GUILD, "dj_role_id", nil)
settings = H.get_guild_settings(TEST_GUILD)
check("set_guild_setting volume persisted", tonumber(settings.volume) == 77)
check("set_guild_setting loop_mode persisted", settings.loop_mode == "song")

-- queue lifecycle
local uid1 = H.enqueue_track(TEST_GUILD, "https://example.com/a", "Track A", TEST_USER)
local uid2 = H.enqueue_track(TEST_GUILD, "https://example.com/b", "Track B", TEST_USER)
local uid3 = H.insert_queue_front(TEST_GUILD, "https://example.com/z", "Track Z (front)", TEST_USER)
check("queue_count after 3 inserts", H.queue_count(TEST_GUILD) == 3)
local rows = H.q("SELECT video_url, title FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic' ORDER BY id ASC", TEST_GUILD)
check("insert_queue_front puts Z first", rows and rows[1] and rows[1].title == "Track Z (front)")

H.snapshot_queue_backup(TEST_GUILD)
check("backup_count matches after snapshot", H.backup_count(TEST_GUILD) == 3)

local n = H.shuffle_queue_rows(TEST_GUILD, true)
check("shuffle_queue_rows returns count", n == 3)

H.delete_backup_track(TEST_GUILD, uid1, nil, nil)
check("delete_backup_track by track_uid", H.backup_count(TEST_GUILD) == 2)

-- clear queue, then restore from backup
H.q("DELETE FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic'", TEST_GUILD)
check("queue emptied", H.queue_count(TEST_GUILD) == 0)
local restored = H.restore_queue_from_backup(TEST_GUILD)
check("restore_queue_from_backup restores 2", restored == 2 and H.queue_count(TEST_GUILD) == 2)

-- track intelligence / affinity / cooccurrence / outcome / feedback
local ok1, err1 = pcall(H.record_track_queued, TEST_GUILD, "https://example.com/a", "Track A", TEST_USER)
check("record_track_queued", ok1, err1)
local ok2, err2 = pcall(H.record_track_play_started, TEST_GUILD, "https://example.com/a", "Track A", TEST_USER)
check("record_track_play_started", ok2, err2)
local ok3, err3 = pcall(H.record_track_cooccurrence, TEST_GUILD, "https://example.com/a", "Track A", "https://example.com/b", "Track B")
check("record_track_cooccurrence", ok3, err3)
local ok4, err4 = pcall(H.record_track_outcome, TEST_GUILD, "https://example.com/a", "Track A", TEST_USER, "finished", 120)
check("record_track_outcome finished", ok4, err4)
local ok5, err5 = pcall(H.record_track_outcome, TEST_GUILD, "https://example.com/b", "Track B", TEST_USER, "skipped", 5)
check("record_track_outcome skipped", ok5, err5)
local ok6, err6 = pcall(H.record_track_feedback, TEST_GUILD, TEST_USER, "https://example.com/a", "Track A", true)
check("record_track_feedback like", ok6, err6)
local ok7, err7 = pcall(H.record_track_feedback, TEST_GUILD, TEST_USER2, "https://example.com/b", "Track B", false)
check("record_track_feedback dislike", ok7, err7)

-- re-run record_track_queued to confirm ON CONFLICT increments (not a duplicate-key crash)
-- NOTE: queued_count is expected to be 3 here, not 2 -- enqueue_track(uid1) above
-- already calls record_track_queued once internally for this same URL, then the
-- explicit "record_track_queued" check above is a second bump, and this re-run
-- is a third. (Original assertion in this test hardcoded 2, which undercounted
-- enqueue_track's own internal call; fixed to match actual, correct behavior.)
local ok8, err8 = pcall(H.record_track_queued, TEST_GUILD, "https://example.com/a", "Track A", TEST_USER)
check("record_track_queued increments on conflict", ok8, err8)
local ti = H.q1("SELECT queued_count, play_count, finish_count, like_count FROM harmonic_track_intelligence WHERE guild_id = %s AND url_key = %s", TEST_GUILD, H.track_key("https://example.com/a", "Track A"))
check("track_intelligence queued_count == 3", ti and tonumber(ti.queued_count) == 3, ti and tostring(ti.queued_count))

-- autodj toggle
H.set_autodj_enabled(TEST_GUILD, true)
check("autodj enabled true", H.get_autodj_enabled(TEST_GUILD) == true)
H.set_autodj_enabled(TEST_GUILD, false)
check("autodj enabled false", H.get_autodj_enabled(TEST_GUILD) == false)

-- smart recommendation query (exercises the full weighted-decay SQL)
local ok9, rec = pcall(H.build_smart_recommendation, TEST_GUILD, { TEST_USER })
check("build_smart_recommendation runs", ok9 and rec and rec.query ~= nil, rec)

local ok10, avoid = pcall(H.load_smart_avoid_keys, TEST_GUILD, { TEST_USER2 })
check("load_smart_avoid_keys runs", ok10, avoid)

-- playback_state upsert/clear
local ok11, err11 = pcall(H.persist_playback_state, TEST_GUILD, "111", "https://example.com/a", "Track A", 42, true, false, uid1)
check("persist_playback_state upsert", ok11, err11)
local ps = H.q1("SELECT position_seconds, is_playing FROM harmonic_playback_state WHERE guild_id = %s AND bot_name = 'harmonic'", TEST_GUILD)
check("playback_state position persisted", ps and tonumber(ps.position_seconds) == 42)
H.clear_playback_state(TEST_GUILD)
ps = H.q1("SELECT video_url, is_playing FROM harmonic_playback_state WHERE guild_id = %s AND bot_name = 'harmonic'", TEST_GUILD)
check("clear_playback_state clears", ps and ps.video_url == nil and ps.is_playing == false)

-- cleanup test rows
H.q("DELETE FROM harmonic_queue WHERE guild_id = %s AND bot_name = 'harmonic'", TEST_GUILD)
H.q("DELETE FROM harmonic_queue_backup WHERE guild_id = %s AND bot_name = 'harmonic'", TEST_GUILD)
H.q("DELETE FROM harmonic_playback_state WHERE guild_id = %s AND bot_name = 'harmonic'", TEST_GUILD)
H.q("DELETE FROM harmonic_guild_settings WHERE guild_id = %s", TEST_GUILD)
H.q("DELETE FROM harmonic_swarm_toggles WHERE guild_id = %s", TEST_GUILD)
H.q("DELETE FROM harmonic_track_intelligence WHERE guild_id = %s", TEST_GUILD)
H.q("DELETE FROM harmonic_user_track_affinity WHERE guild_id = %s", TEST_GUILD)
H.q("DELETE FROM harmonic_track_cooccurrence WHERE guild_id = %s", TEST_GUILD)
print("Cleanup complete.")
