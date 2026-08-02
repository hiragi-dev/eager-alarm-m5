/*
 * eager-alarm-edge for M5StickS3
 * -------------------------------------------------------------------------
 * hiragi-dev/eager-alarm-edge (Rust / Raspberry Pi) の MQTT API v2 を
 * M5StickS3 (ESP32-S3) 上に移植したもの。
 *
 *   - MQTT over TLS で eager-alarm/<device_id>/command を購読
 *   - add / edit / delete / list / pause / stop / status / ringing_status
 *   - 曜日繰り返しアラーム (time + days_of_week + is_enabled + stop_method_id)
 *   - 鳴動は内蔵スピーカー (ES8311 + AW8737) で1秒ごとにビープ
 *   - アラーム設定と鳴動状態は NVS に保存し、再起動後に復元 (alarms.json 相当)
 *
 * 必要なもの:
 *   ボードマネージャ  M5Stack >= 3.2.5 / ボード = M5StickS3
 *   ライブラリ        M5Unified >= 0.2.12, M5GFX >= 0.2.18,
 *                     PubSubClient (knolleary), ArduinoJson >= 7.0
 * -------------------------------------------------------------------------
 */

#include <ArduinoJson.h>
#include <M5Unified.h>
#include <Preferences.h>
#include <PubSubClient.h>
#include <WiFi.h>
#include <WiFiClientSecure.h>
#include <algorithm>
#include <esp_random.h>
#include <time.h>
#include <vector>

#include "secrets.h" // Wi-Fi / MQTT の資格情報 (git 管理外)

// ===================== ユーザー設定 =====================
static const char *WIFI_SSID = SECRET_WIFI_SSID;
static const char *WIFI_PASS = SECRET_WIFI_PASS;

static const char *MQTT_HOST = SECRET_MQTT_HOST;
static const uint16_t MQTT_PORT = 8883;
static const char *MQTT_USER = SECRET_MQTT_USER;
static const char *MQTT_PASS = SECRET_MQTT_PASS;

// トピックの {device_id}。Pi と同時に動かすなら別の値にすること
static const char *DEVICE_ID = "sticks3";
static const char *MQTT_CLIENT_ID = "sticks3";

// タイムゾーン (POSIX TZ 形式)。JST は "JST-9"
static const char *TZ_INFO = "JST-9";
static const char *NTP1 = "ntp.nict.jp";
static const char *NTP2 = "pool.ntp.org";

// スピーカー音量。バッテリー駆動時は 75% 未満推奨 (=190 以下)
static const uint8_t SPK_VOLUME = 150;

// 再起動時に鳴動状態を復元する猶予 (秒)。
// 電源断の直前に鳴っていたアラームは、鳴り始めからこの秒数以内なら復帰後も鳴り続ける
// (瞬断で目覚ましが黙ってしまうのを防ぐため)。これを超えたものは「もう時間が過ぎた
// アラーム」とみなして復元せず、次回の予定に回す。
// 0 にすると鳴動状態を一切復元しない (Rust 版は無条件に復元する)。
static const time_t RINGING_RESUME_GRACE_SEC = 300; // 5 分

// 1 = ESP32 内蔵のルート証明書バンドルで検証 (推奨)
// 0 = 証明書検証なし (動作確認用。本番では使わない)
#define USE_CERT_BUNDLE 1
#if USE_CERT_BUNDLE
extern const uint8_t
    rootca_crt_bundle_start[] asm("_binary_x509_crt_bundle_start");
extern const uint8_t rootca_crt_bundle_end[] asm("_binary_x509_crt_bundle_end");
#endif
// =======================================================

// ---------- アラームモデル ----------
struct Alarm {
  String id; // UUID v4
  uint8_t hour = 0;
  uint8_t minute = 0;
  uint8_t days = 0; // bit n = tm_wday n (bit0=Sun ... bit6=Sat)
  bool enabled = true;
  bool hasStopMethod = false;
  String stopMethodId; // hasStopMethod == false なら null 扱い

  time_t nextWakeup = 0; // 0 = スケジュールなし
  bool ringing = false;
  time_t ringingSince = 0; // 鳴り始めた予定時刻 (ringing == false なら 0)
 
  bool isNfcEnabled; // NFCを使った二要素認証のアラームかどうか
  bool isNfcVerified; // NFC認証が成功したかどうか
};

static std::vector<Alarm> g_alarms;

// NVS から読んだ鳴動状態の復元待ち。時刻が確定してから restoreRinging()
// で判定する
struct RingRestore {
  String id;
  time_t since;
};
static std::vector<RingRestore> g_ringRestore;

// NTP 同期後のスケジュール組み直しが済んだか。済むまでアラームは発火させない
static bool g_scheduleReady = false;

// pause によるミュート期間 (Rust の MuteStatus 相当)
static bool g_muteActive = false;
static uint32_t g_muteUntilMs = 0;

static WiFiClientSecure g_net;
static PubSubClient g_mqtt(g_net);
static Preferences g_prefs;

static String T_COMMAND, T_ALARMS, T_STATUS, T_RINGING;

// callback 内では publish せず、ここに積んで loop() で処理する
static std::vector<String> g_pending;

// ---------- ユーティリティ ----------
static const char *WD_NAMES[7] = {"Sun", "Mon", "Tue", "Wed",
                                  "Thu", "Fri", "Sat"};
static const int WD_ORDER[7] = {1, 2, 3, 4, 5, 6, 0}; // 出力は Mon..Sun 順

static int wdayFromName(const char *s) {
  for (int i = 0; i < 7; i++) {
    if (strcasecmp(s, WD_NAMES[i]) == 0)
      return i;
  }
  return -1;
}

static String makeUuidV4() {
  uint8_t b[16];
  esp_fill_random(b, sizeof(b));
  b[6] = (b[6] & 0x0F) | 0x40;
  b[8] = (b[8] & 0x3F) | 0x80;
  char buf[37];
  snprintf(
      buf, sizeof(buf),
      "%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x-%02x%02x%02x%02x%02x%02x",
      b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], b[8], b[9], b[10], b[11],
      b[12], b[13], b[14], b[15]);
  return String(buf);
}

static bool timeIsSynced() {
  return time(nullptr) > 1700000000; // 2023-11 以降なら同期済みとみなす
}

static bool isMuted() {
  if (!g_muteActive)
    return false;
  if ((int32_t)(millis() - g_muteUntilMs) >= 0) {
    g_muteActive = false;
    return false;
  }
  return true;
}

static Alarm *findAlarm(const String &id) {
  for (auto &a : g_alarms) {
    if (a.id == id)
      return &a;
  }
  return nullptr;
}

/*
 * 次の発火時刻を求める。Rust 版 Alarm::next_wakeup_from と同じ挙動:
 *   - 無効 or 曜日が空なら発火しない
 *   - 1秒の猶予を持たせ、わずかに過去の時刻は "今すぐ発火" とみなす
 *   - その場合の発火時刻は from (=now) 側に丸める
 */
static time_t computeNextWakeup(const Alarm &a, time_t from) {
  if (!a.enabled || a.days == 0)
    return 0;

  struct tm base;
  localtime_r(&from, &base);

  for (int i = 0; i < 8; i++) {
    struct tm cand = base;
    cand.tm_mday += i;
    cand.tm_hour = a.hour;
    cand.tm_min = a.minute;
    cand.tm_sec = 0;
    cand.tm_isdst = -1;

    time_t c = mktime(&cand); // ここで日付が正規化される
    if (c == (time_t)-1)
      continue;

    struct tm norm;
    localtime_r(&c, &norm);
    if ((a.days & (1 << norm.tm_wday)) == 0)
      continue;

    if (c + 1 > from) { // candidate + tolerance > now
      return (c > from) ? c : from;
    }
  }
  return 0;
}

static void rescheduleAll(time_t from) {
  for (auto &a : g_alarms) {
    a.nextWakeup = computeNextWakeup(a, from);
  }
}

// ---------- 永続化 (Rust の alarms.json 相当 / NVS に保存) ----------
static void alarmToJson(const Alarm &a, JsonObject o) {
  o["id"] = a.id;
  char t[6];
  snprintf(t, sizeof(t), "%02u:%02u", a.hour, a.minute);
  o["time"] = t;
  JsonArray days = o["days_of_week"].to<JsonArray>();
  for (int i = 0; i < 7; i++) {
    int w = WD_ORDER[i];
    if (a.days & (1 << w))
      days.add(WD_NAMES[w]);
  }
  o["is_enabled"] = a.enabled;
  if (a.hasStopMethod) {
    o["stop_method_id"] = a.stopMethodId;
  } else {
    o["stop_method_id"] = nullptr;
  }
  o["is_nfc_enabled"] = a.isNfcEnabled;
  o["is_nfc_verified"] = a.isNfcVerified;
}

static void persistState() {
  JsonDocument doc;
  JsonArray arr = doc["alarms"].to<JsonArray>();
  for (const auto &a : g_alarms)
    alarmToJson(a, arr.add<JsonObject>());
  // 鳴動中のアラームは「いつ鳴り始めたか」も残す (再起動時の復元判定に使う)
  JsonArray ring = doc["ringing"].to<JsonArray>();
  for (const auto &a : g_alarms) {
    if (!a.ringing)
      continue;
    JsonObject o = ring.add<JsonObject>();
    o["id"] = a.id;
    o["since"] = (int64_t)a.ringingSince;
  }

  String out;
  serializeJson(doc, out);
  g_prefs.putString("state", out); // NVS の文字列上限に注意 (~4000 バイト)
}

static void loadState() {
  String raw = g_prefs.getString("state", "");
  if (raw.length() == 0)
    return;

  JsonDocument doc;
  if (deserializeJson(doc, raw)) {
    Serial.println("[store] 保存データが壊れています。空で起動します");
    return;
  }

  JsonArrayConst arr = doc["alarms"].as<JsonArrayConst>();
  for (JsonObjectConst o : arr) {
    Alarm a;
    a.id = String(o["id"].as<const char *>());
    const char *t = o["time"] | "00:00";
    a.hour = atoi(t);
    a.minute = atoi(t + 3);
    for (JsonVariantConst d : o["days_of_week"].as<JsonArrayConst>()) {
      int w = wdayFromName(d.as<const char *>());
      if (w >= 0)
        a.days |= (1 << w);
    }
    a.enabled = o["is_enabled"] | true;
    if (!o["stop_method_id"].isNull()) {
      a.hasStopMethod = true;
      a.stopMethodId = String(o["stop_method_id"].as<const char *>());
    }
    g_alarms.push_back(a);
  }

  // 終了時に鳴動中だったアラーム。ここでは ringing を立てない:
  // NTP 同期前は「もう時間が過ぎたアラームか」を判定できないため、
  // 時刻が確定してから restoreRinging() で判断する
  for (JsonObjectConst o : doc["ringing"].as<JsonArrayConst>()) {
    const char *id = o["id"];
    if (!id)
      continue;
    g_ringRestore.push_back({String(id), (time_t)(o["since"] | (int64_t)0)});
  }
}

/*
 * 再起動前に鳴っていたアラームの鳴動を復元する。時計が確定してから一度だけ呼ぶこと。
 * Rust 版 (with_ringer_and_store) は ringing_ids を無条件に start_ringing
 * するが、 こちらは鳴り始めから RINGING_RESUME_GRACE_SEC
 * 以内のものだけを復元する。
 * 電源が落ちている間に時刻が過ぎてしまったアラームは起動直後に鳴り出さず、
 * 次回の予定 (computeNextWakeup) に回る。
 */
static void restoreRinging() {
  time_t now = time(nullptr);
  for (const auto &r : g_ringRestore) {
    Alarm *a = findAlarm(r.id);
    if (!a)
      continue;
    if (r.since <= 0 || now - r.since > RINGING_RESUME_GRACE_SEC) {
      Serial.printf("[boot] %s は時間が過ぎているため鳴動を復元しません\n",
                    a->id.c_str());
      continue;
    }
    a->ringing = true;
    a->ringingSince = r.since;
    Serial.printf("[boot] %s の鳴動を再開します\n", a->id.c_str());
  }
  g_ringRestore.clear();
  persistState();
}

// ---------- MQTT ----------
static void publishAlarms() {
  std::vector<const Alarm *> sorted;
  for (const auto &a : g_alarms)
    sorted.push_back(&a);
  std::sort(sorted.begin(), sorted.end(), [](const Alarm *x, const Alarm *y) {
    return (x->hour * 60 + x->minute) < (y->hour * 60 + y->minute);
  });

  JsonDocument doc;
  JsonArray arr = doc.to<JsonArray>();
  for (const Alarm *a : sorted)
    alarmToJson(*a, arr.add<JsonObject>());

  String out;
  serializeJson(doc, out);
  g_mqtt.publish(T_ALARMS.c_str(), out.c_str());
}

static void publishRingingStatus() {
  JsonDocument doc;
  JsonArray ids = doc["ringing_ids"].to<JsonArray>();
  for (const auto &a : g_alarms) {
    if (a.ringing)
      ids.add(a.id);
  }
  doc["is_ringing"] = ids.size() > 0;

  String out;
  serializeJson(doc, out);
  g_mqtt.publish(T_RINGING.c_str(), out.c_str());
}

static void publishStatus() {
  g_mqtt.publish(T_STATUS.c_str(), "{\"online\":true}");
}

static void stopAllRinging() {
  std::vector<String> stopped;
  for (auto &a : g_alarms) {
    if (a.ringing) {
      a.ringing = false;
      a.isNfcVerified = false; // 停止時に NFC 認証をリセットする
      a.ringingSince = 0;
      stopped.push_back(a.id);
    }
  }

  // 今止めたアラームだけ +2 秒を起点にして、猶予1秒以内での即再発火を防ぐ。
  // 待機中だったアラームは now を起点に通常どおり組み直す。
  time_t now = time(nullptr);
  for (auto &a : g_alarms) {
    bool wasRinging =
        std::find(stopped.begin(), stopped.end(), a.id) != stopped.end();
    a.nextWakeup = computeNextWakeup(a, wasRinging ? now + 2 : now);
  }
  persistState();
}

// アラーム1件を JSON から組み立てる (add / edit 共通)
static bool parseAlarmFields(JsonDocument &doc, Alarm &a) {
  const char *t = doc["time"];
  if (!t || strlen(t) < 4)
    return false;
  a.hour = atoi(t);
  a.minute = atoi(t + 3);
  if (a.hour > 23 || a.minute > 59)
    return false;

  a.days = 0;
  for (JsonVariantConst d : doc["days_of_week"].as<JsonArrayConst>()) {
    int w = wdayFromName(d.as<const char *>());
    if (w >= 0)
      a.days |= (1 << w);
  }
  a.enabled = doc["is_enabled"] | true;

  if (!doc["stop_method_id"].isNull()) {
    a.hasStopMethod = true;
    a.stopMethodId = String(doc["stop_method_id"].as<const char *>());
  } else {
    a.hasStopMethod = false;
    a.stopMethodId = "";
  }

  a.isNfcEnabled = doc["is_nfc_enabled"] | false;
  a.isNfcVerified = doc["is_nfc_verified"] | false;

  return true;
}

static void handleCommand(const String &payload) {
  JsonDocument doc;
  if (deserializeJson(doc, payload)) {
    Serial.printf("[mqtt] 不正なペイロード: %s\n", payload.c_str());
    return;
  }
  const char *type = doc["type"];
  if (!type)
    return;

  time_t now = time(nullptr);

  if (strcmp(type, "add") == 0) {
    Alarm a;
    a.id = makeUuidV4();
    if (!parseAlarmFields(doc, a))
      return;


    a.nextWakeup = computeNextWakeup(a, now);
    g_alarms.push_back(a);
    persistState();
    Serial.printf("[cmd] added %s %02u:%02u %s\n", a.id.c_str(), a.hour, a.minute, a.isNfcEnabled ? "NFC" : "no NFC");

  } else if (strcmp(type, "edit") == 0) {
    const char *id = doc["id"];
    if (!id)
      return;
    Alarm a;
    a.id = String(id);
    if (!parseAlarmFields(doc, a))
      return;
    Alarm *old = findAlarm(a.id);
    if (old) {
      *old = a; // 全置換 (フィールドのマージはしない)
    } else {
      g_alarms.push_back(a); // Rust 版と同じく未知の id なら新規作成
    }
    rescheduleAll(now);
    persistState();
    Serial.printf("[cmd] edited %s %s\n", a.id.c_str(), a.isNfcEnabled ? "NFC" : "no NFC");

  } else if (strcmp(type, "delete") == 0) {
    const char *id = doc["id"];
    if (!id)
      return;
    String target(id);
    g_alarms.erase(
        std::remove_if(g_alarms.begin(), g_alarms.end(),
                       [&](const Alarm &a) { return a.id == target; }),
        g_alarms.end());
    rescheduleAll(now);
    persistState();
    Serial.printf("[cmd] deleted %s\n", target.c_str());

  } else if (strcmp(type, "list") == 0) {
    publishAlarms();

  } else if (strcmp(type, "ringing_status") == 0) {
    publishRingingStatus();

  } else if (strcmp(type, "pause") == 0) {
    Alarm *ringing_alarm = nullptr;
    for (const auto &a : g_alarms) {
      if (a.ringing) {
        ringing_alarm = const_cast<Alarm *>(&a);
        break;
      }
    }

    if (!ringing_alarm) {
      Serial.printf("[cmd] nfc_verify failed: no ringing alarm found\n");
      return;
    }

    if (ringing_alarm->isNfcEnabled && !ringing_alarm->isNfcVerified) {
      Serial.printf("[cmd] pause failed: NFC認証が必要なアラームです\n");
      return;
    }

    uint32_t ms = doc["duration_ms"] | 0;
    g_muteUntilMs = millis() + ms; // 上書き。積み上げない
    g_muteActive = ms > 0;
    Serial.printf("[cmd] paused %u ms\n", ms);

  } else if (strcmp(type, "verify_nfc") == 0) {
    Alarm *ringing_alarm = nullptr;
    for (const auto &a : g_alarms) {
      if (a.ringing) {
        ringing_alarm = const_cast<Alarm *>(&a);
        break;
      }
    }

    if (!ringing_alarm) {
      Serial.printf("[cmd] nfc_verify failed: no ringing alarm found\n");
      return;
    }

    ringing_alarm->isNfcVerified = true;
    persistState();
    Serial.printf("[cmd] nfc_verify succeeded for %s\n", ringing_alarm->id.c_str());
  } else if (strcmp(type, "stop") == 0) {
    Alarm *ringing_alarm = nullptr;
    for (const auto &a : g_alarms) {
      if (a.ringing) {
        ringing_alarm = const_cast<Alarm *>(&a);
        break;
      }
    }

    if (!ringing_alarm) {
      Serial.printf("[cmd] stop failed: no ringing alarm found\n");
      stopAllRinging();
      return;
    }

    if (ringing_alarm->isNfcEnabled && !ringing_alarm->isNfcVerified) {
      Serial.printf("[cmd] stop failed: NFC認証が必要なアラームです\n");
      return;
    }
    
    stopAllRinging();
    Serial.println("[cmd] stopped all ringing alarms");

  } else if (strcmp(type, "status") == 0) {
    publishStatus();
  }
}

static void mqttCallback(char *topic, byte *payload, unsigned int len) {
  String s;
  s.reserve(len + 1);
  for (unsigned int i = 0; i < len; i++)
    s += (char)payload[i];
  if (g_pending.size() < 8)
    g_pending.push_back(s);
}

static void ensureWifi() {
  if (WiFi.status() == WL_CONNECTED)
    return;
  static uint32_t last = 0;
  if (millis() - last < 5000)
    return;
  last = millis();
  WiFi.begin(WIFI_SSID, WIFI_PASS);
}

static void ensureMqtt() {
  if (WiFi.status() != WL_CONNECTED || g_mqtt.connected())
    return;
  static uint32_t last = 0;
  if (millis() - last < 3000)
    return;
  last = millis();

  if (g_mqtt.connect(MQTT_CLIENT_ID, MQTT_USER, MQTT_PASS)) {
    // PubSubClient は QoS 0/1 のみ。Rust 版の QoS2 購読とはここが異なる
    g_mqtt.subscribe(T_COMMAND.c_str(), 1);
    Serial.println("[mqtt] connected");
  } else {
    Serial.printf("[mqtt] connect failed rc=%d\n", g_mqtt.state());
  }
}

// ---------- 鳴動 & 画面 ----------
static void checkSchedule() {
  // NTP 同期前に組んだ nextWakeup は 1970 年基準ででたらめなので、
  // 同期後の組み直しが済むまでは絶対に発火させない
  if (!g_scheduleReady)
    return;
  time_t now = time(nullptr);
  bool changed = false;

  for (auto &a : g_alarms) {
    if (a.nextWakeup == 0 || now < a.nextWakeup)
      continue;
    if (!a.ringing) {
      a.ringing = true;
      a.ringingSince = a.nextWakeup;
      Serial.printf("[ring] %s %02u:%02u\n", a.id.c_str(), a.hour, a.minute);
    }
    // 発火後は +2 秒を起点に次回を計算する (同日再発火の防止)
    a.nextWakeup = computeNextWakeup(a, a.nextWakeup + 2);
    changed = true;
  }
  if (changed)
    persistState();
}

static bool anyRinging() {
  for (const auto &a : g_alarms) {
    if (a.ringing)
      return true;
  }
  return false;
}

static void ringTick() {
  static uint32_t last = 0;
  if (millis() - last < 1000)
    return;
  last = millis();
  if (anyRinging() && !isMuted()) {
    Alarm *ringing_alarm = nullptr;
    for (const auto &a : g_alarms) {
      if (a.ringing) {
        ringing_alarm = const_cast<Alarm *>(&a);
        break;
      }
    }

    if (!ringing_alarm) {
      Serial.println("[ring] error: no ringing alarm found");
      return;
    }

    if (ringing_alarm->isNfcVerified) {
      M5.Speaker.tone(2000, 250);
    } else {
      M5.Speaker.tone(2000, 450);
    }

    publishRingingStatus();
  }
}

static void drawUi() {
  static uint32_t last = 0;
  if (millis() - last < 500)
    return;
  last = millis();

  static M5Canvas canvas(&M5.Display);
  static bool inited = false;
  if (!inited) {
    canvas.createSprite(M5.Display.width(), M5.Display.height());
    inited = true;
  }

  bool ringing = anyRinging();
  canvas.fillSprite(ringing && !isMuted() ? TFT_RED : TFT_BLACK);
  canvas.setTextColor(TFT_WHITE);
  canvas.setTextFont(&fonts::Font0);

  char buf[64];
  if (timeIsSynced()) {
    time_t now = time(nullptr);
    struct tm t;
    localtime_r(&now, &t);
    canvas.setTextSize(3);
    snprintf(buf, sizeof(buf), "%02d:%02d:%02d", t.tm_hour, t.tm_min, t.tm_sec);
    canvas.drawString(buf, 8, 8);
  } else {
    canvas.setTextSize(2);
    canvas.drawString("time syncing...", 8, 10);
  }

  canvas.setTextSize(1);
  snprintf(buf, sizeof(buf), "WiFi:%s  MQTT:%s",
           WiFi.status() == WL_CONNECTED ? "OK" : "--",
           g_mqtt.connected() ? "OK" : "--");
  canvas.drawString(buf, 8, 42);

  snprintf(buf, sizeof(buf), "alarms:%u", (unsigned)g_alarms.size());
  canvas.drawString(buf, 8, 56);

  // 直近の予定を表示
  time_t soonest = 0;
  for (const auto &a : g_alarms) {
    if (a.nextWakeup && (soonest == 0 || a.nextWakeup < soonest))
      soonest = a.nextWakeup;
  }
  if (soonest) {
    struct tm t;
    localtime_r(&soonest, &t);
    snprintf(buf, sizeof(buf), "next: %s %02d:%02d", WD_NAMES[t.tm_wday],
             t.tm_hour, t.tm_min);
    canvas.drawString(buf, 8, 70);
  }

  if (ringing) {
    canvas.setTextSize(2);
    canvas.drawString(isMuted() ? "PAUSED" : "RINGING", 8, 90);
  }
  canvas.setTextSize(1);
  canvas.drawString("BtnA:stop  BtnB:pause60s", 8, 118);

  canvas.pushSprite(0, 0);
}

// ---------- setup / loop ----------
void setup() {
  auto cfg = M5.config();
  M5.begin(cfg);
  M5.Display.setRotation(1);
  M5.Speaker.begin();
  M5.Speaker.setVolume(SPK_VOLUME);
  Serial.begin(115200);

  T_COMMAND = String("eager-alarm/") + DEVICE_ID + "/command";
  T_ALARMS = String("eager-alarm/") + DEVICE_ID + "/alarms";
  T_STATUS = String("eager-alarm/") + DEVICE_ID + "/status";
  T_RINGING = String("eager-alarm/") + DEVICE_ID + "/ringing_status";

  g_prefs.begin("eager-alarm", false);
  loadState();

  WiFi.mode(WIFI_STA);
  WiFi.setAutoReconnect(true);
  WiFi.begin(WIFI_SSID, WIFI_PASS);

  configTzTime(TZ_INFO, NTP1, NTP2);

#if USE_CERT_BUNDLE
  g_net.setCACertBundle(rootca_crt_bundle_start,
                        rootca_crt_bundle_end - rootca_crt_bundle_start);
#else
  g_net.setInsecure();
#endif

  g_mqtt.setServer(MQTT_HOST, MQTT_PORT);
  g_mqtt.setCallback(mqttCallback);
  g_mqtt.setBufferSize(4096); // list の応答が 256 バイトを超えるため必須
  g_mqtt.setKeepAlive(15);

  // ここではスケジュールを組まない。起動直後の時刻は 1970 年で意味がないため、
  // 時計が確定してから loop() で一度だけ組む
}

void loop() {
  M5.update();

  // 時計が確定したタイミングで一度だけスケジュールを組み、
  // 再起動前の鳴動状態もここで判定する (どちらも正しい現在時刻が要る)
  if (!g_scheduleReady && timeIsSynced()) {
    rescheduleAll(time(nullptr));
    restoreRinging();
    g_scheduleReady = true;
  }

  // 本体ボタン (MQTT の stop / pause と同等の操作)
  if (M5.BtnA.wasPressed()) {
    stopAllRinging();
  }
  if (M5.BtnB.wasPressed()) {
    g_muteUntilMs = millis() + 60000;
    g_muteActive = true;
  }

  ensureWifi();
  ensureMqtt();
  g_mqtt.loop();

  while (!g_pending.empty()) {
    String cmd = g_pending.front();
    g_pending.erase(g_pending.begin());
    handleCommand(cmd);
  }

  checkSchedule();
  ringTick();
  drawUi();
}
