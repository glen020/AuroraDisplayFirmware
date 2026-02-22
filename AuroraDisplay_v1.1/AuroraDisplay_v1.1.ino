/*******************************************************
  AuroraDisplay / WeatherClk - Wemos D1 Mini ESP32
  ------------------------------------------------------
  FULL REWRITE (STRUCTURE + FORWARDS + QUIET MODE):
  ✅ Proper forward declarations (grouped & commented)
  ✅ Added `quiet` parameter to check-in/update path
  ✅ Replaced the ~37x debug `delay(1000)` calls with qDelay(quiet, 1000)
     - Loud (quiet=false): keeps your "slow debug stepping"
     - Quiet (quiet=true): runs fast, no screen spam, no 1s pauses
  ✅ Wrapped check-in status screens so loop() check-ins can be silent
  ✅ No logic changes outside of the check-in quiet wrapping + forward cleanup
*******************************************************/

// =====================================================
// NOTES / TODO (kept from your original comments)
// =====================================================
//
// WEMOS D1 MINI ESP32 !!!!! This board
// jan 10 - We hardcoded the download it - Need to show progress on Screen  of the down load.
// IN the Flask app we just need to rename it to the 6 character filename instead of a 1-9 index and reload up to the web
// Jan 26 - Tried adding the new code for config file check in VS the hardcoded fetch. Still need to upload to server new code and test (not sure how to test even right now, fiugure that out)_
//
// Install Notes - Partition as large as can be
// Upload File via Uploader Little FS
// WIP - only 5 frames in bin, Use colab to do total conversion. Then remove header file, then add to little fs and make animation instead
// Havethe testing code to make a display case. 2x2 displays - big power supply
//
// Instructions
/*
hold touch 5 seconds - whats that mean
Sometimes on Connection it acts like a hotel gateway wifi, threee dots use connection as is
Updates at 6 AM and 6 PM for forecast.
Hourly Weather updates on top of the hour
Time zone?
Brightness - 1-5
Sleep mode whats it do
FYI Sleepmode 0 Works 1 /8
Sleep Settings (also need to test these in debug mode)
openweather website to check if your city will be first
*/


//Cleaned


#ifndef CONFIG_ARDUINO_LOOP_STACK_SIZE
#define CONFIG_ARDUINO_LOOP_STACK_SIZE 16384
#endif





// =====================================================
// INCLUDES
// =====================================================

// ESP32 system/debug helpers
#include "esp_heap_caps.h"
#include "esp_system.h"  // esp_reset_reason()

// Custom 3x5 font
#include "CustomFont3x5.h"

// Icon bitmaps (clouds, etc.)
#include "icons.h"

// Core networking
#include <WiFi.h>
#include <WiFiUdp.h>

// HTTP + JSON parsing
#include <HTTPClient.h>
#include <ArduinoJson.h>

// Time + math
#include <NTPClient.h>
#include <time.h>
#include <math.h>

// HUB75 display driver
#include <ESP32-HUB75-MatrixPanel-I2S-DMA.h>

// WiFi captive portal
#include <WiFiManager.h>  // https://github.com/tzapu/WiFiManager

// Filesystem
#include "LittleFS.h"

// Secure client support (downloads)
#include <WiFiClientSecure.h>

// Misc
#include <memory>


// =====================================================
// PANEL / DISPLAY CONSTANTS
// =====================================================
#define PANEL_RES_X 64
#define PANEL_RES_Y 32
#define PANEL_CHAIN 1


// =====================================================
// GLOBALS (original behavior retained)
// =====================================================

static bool g_pairShowPairedActive = false;
static uint32_t g_pairShowPairedUntilMs = 0;

String g_lastPairFriendlyName = "";
String g_lastPairOwnerEmail = "";


enum PairFlowState : uint8_t {
  PAIRFLOW_OFF = 0,
  PAIRFLOW_WAIT_CODE,
  PAIRFLOW_WAIT_SUCCESS
};

static PairFlowState g_pairFlow = PAIRFLOW_OFF;

static uint32_t g_pairPhaseStartMs = 0;
static uint32_t g_pairPhaseEndMs = 0;
static uint32_t g_pairNextCheckinMs = 0;
static const uint32_t PAIR_PHASE_MS = 3UL * 60UL * 1000UL;  // 3 minutes
static const uint32_t PAIR_POLL_MS = 10UL * 1000UL;         // 10 seconds

// You need a flag that becomes true when server confirms pairing success.
// Set this based on your check-in JSON response.
static bool g_lastPairSuccess = false;



// Check-in UI result state
static bool g_lastCheckinOk = false;
static bool g_lastCheckinHadPairing = false;
static String g_lastPairCode = "";




// Hourly weather attempt budget
static int g_wxHourKey = -1;  // unique key for current local hour
static uint8_t g_wxAttemptsThisHour = 0;
static uint32_t g_wxRetryAtMs = 0;                        // when 2nd attempt is allowed
static const uint32_t WX_RETRY_DELAY_MS = 90UL * 1000UL;  // retry once after 90s



// Animation/build metadata
int g_animVer = 0;        // Current animation version for current tag
String g_binSha256 = "";  // Last installed BIN sha256
bool g_bootInProgress = true;

// "Animation missing" UI/log state
static bool g_animMissing = false;       // Latch when file has 0 frames
static uint32_t g_animMissingUiMs = 0;   // UI rate limit
static uint32_t g_animMissingLogMs = 0;  // Serial rate limit
static uint32_t g_animMissingShowUntilMs = 0;
static bool g_animMissingNeedsRestore = false;

// NTP periodic resync
static uint32_t lastNtpMs = 0;
const uint32_t NTP_SYNC_MS = 15UL * 60UL * 1000UL;  // 15 minutes

// Worst blocking section tracker
static uint32_t g_worstBlockMs = 0;
static char g_worstBlockName[24] = "none";

static inline void noteBlock(const char* name, uint32_t dt) {
  if (dt > g_worstBlockMs) {
    g_worstBlockMs = dt;
    strncpy(g_worstBlockName, name, sizeof(g_worstBlockName) - 1);
    g_worstBlockName[sizeof(g_worstBlockName) - 1] = '\0';
  }
}

//overlay for pairing
bool g_pairCountdownActive = false;
bool g_pairSuccessPhase = false;
uint16_t g_pairCountdownLastSeconds = 0xFFFF;


// =====================================================
// TIMELINE (JSON-driven frame durations)
// =====================================================
static const uint16_t TL_MIN_MS = 1;
static const uint16_t TL_DEFAULT_MS = 100;

// Max frames we can time in RAM.
// 2 bytes per entry, 4096 entries = 8 KB.
static const int TL_MAX_FRAMES = 4096;

static uint16_t g_timelineDurMs[TL_MAX_FRAMES];
static int g_timelineCount = 0;
static bool g_timelineLoaded = false;

// Quick clamp helper for timeline values
static inline uint16_t tlClampMs(int v) {
  if (v < (int)TL_MIN_MS) return TL_MIN_MS;
  if (v > 60000) return 60000;
  return (uint16_t)v;
}



// =====================================================
// WEATHER/ANIM CYCLE (UI_WEATHER day mode)
// =====================================================
static uint32_t g_weatherPhaseStartMs = 0;  // Time we entered weather phase


// =====================================================
// UI MODE AUTO-TIMEOUT (seconds)
// =====================================================

// CLOCK mode auto-exit timeout (0 = never auto-exit)
int g_clockModeTimeoutSeconds = 60;

// ANIM mode auto-exit timeout (0 = never auto-exit)
int g_animModeTimeoutSeconds = 60;

// Deadline to revert back to UI_WEATHER (0 = no deadline)
static uint32_t g_uiModeUntilMs = 0;


// ---- Network throttle / backoff ----
static uint32_t g_netBackoffUntilMs = 0;
static uint8_t g_netFailStreak = 0;
static uint32_t g_lastNetBlockMs = 0;   // Last blocking op duration
static uint32_t g_netBlockMsTotal = 0;  // Cumulative between check-ins
static uint32_t g_netBlockMs = 0;


// Clamp helper for integer ranges
int clampSecs(int v, int minV, int maxV) {
  if (v < minV) return minV;
  if (v > maxV) return maxV;
  return v;
}

static inline bool netBackoffActive() {
  return (int32_t)(millis() - g_netBackoffUntilMs) < 0;
}

static inline void noteNetResult(bool ok, uint32_t blockMs) {
  g_netBlockMs = blockMs;
  g_netBlockMsTotal += blockMs;

  if (ok) {
    g_netFailStreak = 0;
    g_netBackoffUntilMs = 0;
  } else {
    if (g_netFailStreak < 10) g_netFailStreak++;
    uint32_t backoff = 1000UL << (g_netFailStreak > 6 ? 6 : g_netFailStreak);  // Capped exponential backoff
    if (backoff > 60000UL) backoff = 60000UL;
    g_netBackoffUntilMs = millis() + backoff;
  }
}


// =====================================================
// WIFI HARDCODED OVERRIDE (optional)
// =====================================================
const char* hardcodedSSID = "GJNet";
const char* hardcodedPassword = "7802323995";
bool useHardcodedWiFi = true;


// =====================================================
// BUTTON (GPIO33 -> button -> GND, INPUT_PULLUP, pressed = LOW)
// =====================================================
static const int BTN_PIN = 33;
static const uint32_t BTN_DEBOUNCE_MS = 30;
static const uint32_t BTN_LONGPRESS_MS = 5000;

// Stable button tracking
static bool g_btnStablePressed = false;
static bool g_btnLastReading = false;
static uint32_t g_btnChangeMs = 0;

static bool g_btnLongHandled = false;
static uint32_t g_btnPressStartMs = 0;

// Overlay message behavior
static const uint32_t BTN_HOLD_1S_MS = 1000;
static const uint32_t BTN_MSG_SHOW_MS = 1200;
static bool g_btn1sFired = false;
static uint32_t g_btnMsgUntilMs = 0;

// Overlay flags for main loop redraw
static bool g_btnOverlayActive = false;
static bool g_btnNeedsFullRedraw = false;

// Timed-hold info pages
static const uint32_t HOLD_NO_ACTION_MS = 2000;   // 0-2s: no action
static const uint32_t HOLD_PAGE1_END_MS = 10000;  // 2-10s: page 1
static const uint32_t HOLD_PAGE2_END_MS = 20000;  // 10-20s: page 2
static const uint32_t HOLD_PAGE3_END_MS = 30000;  // 20s+: page 3 (clamped)

static bool g_holdActive = false;
static uint8_t g_holdPageShown = 0;  // 0 none, 1..3 pages
static uint32_t g_holdLastUiMs = 0;  // UI refresh throttle


// =====================================================
// NTP TIME
// =====================================================
WiFiUDP ntpUDP;
// Init in UTC; offset is set later from OpenWeather timezone
NTPClient timeClient(ntpUDP, "pool.ntp.org", 0, 60000);



// =====================================================
// WEATHER API CONFIG
// =====================================================
const String weatherApiKey = "aed0805c38cabc459577d9437fc6c51d";
String weatherCity = "Edmonton";
const String weatherUnits = "metric";

// Base URLs now configurable from WiFiManager + persisted config
String g_weatherBaseUrl = "https://api.openweathermap.org/data/2.5";
String g_checkinBaseUrl = "https://www.auroradisplay.ca";

// Portal buffers
char weatherBaseUrlBuf[96] = "https://api.openweathermap.org/data/2.5";
char checkinBaseUrlBuf[96] = "https://www.auroradisplay.ca";

// WiFiManager params
WiFiManagerParameter p_weatherBaseUrl(
  "wxBase",
  "Weather base URL (no trailing slash)",
  weatherBaseUrlBuf,
  sizeof(weatherBaseUrlBuf));

WiFiManagerParameter p_checkinBaseUrl(
  "chkBase",
  "Check-in base URL (no trailing slash)",
  checkinBaseUrlBuf,
  sizeof(checkinBaseUrlBuf));

long g_tzOffsetSeconds = 0;  // dynamic, from OpenWeather
bool g_hasTzOffset = false;

// =====================================================
// DISPLAY INSTANCE + UI COLORS
// =====================================================
MatrixPanel_I2S_DMA* dma_display = nullptr;

// UI colors (set after display init)
uint16_t UI_WHITE;
uint16_t UI_BLACK;
uint16_t UI_YELLOW;
uint16_t UI_BLUE;
uint16_t UI_RED;


// =====================================================
// WEATHER DATA (used by draw routines)
// =====================================================
String globalDescription;
int globalTempActual, globalTempLow, globalTempHigh, globalWindSpeed;
String globalCityName;
String globalIcon;
String globalScrollingText;

// Forecast string shown in scroller
String forecastString = "";

bool weatherReady = false;
bool forecastReady = false;
bool screenDrawnOnce = false;

unsigned long lastFetchRetryMs = 0;
const unsigned long FETCH_RETRY_INTERVAL_MS = 15000;
String lastFetchNote = "";


// Loop/display profiling globals
uint32_t g_worstDisplayMs = 0;
String g_worstDisplayName = "";


// ---- Perf wrappers ----
static inline void noteDisplay(const char* name, uint32_t dt) {
  if (dt > g_worstDisplayMs) {
    g_worstDisplayMs = dt;
    g_worstDisplayName = name;  // String assignment
  }
}

#define WRAP_DISPLAY(name, expr) \
  do { \
    uint32_t __t0 = millis(); \
    expr; \
    noteDisplay((name), millis() - __t0); \
  } while (0)

#define WRAP_BLOCK(name, expr) \
  do { \
    uint32_t __t0 = millis(); \
    expr; \
    noteBlock((name), millis() - __t0); \
  } while (0)

#define WRAP_BLOCK_RET_BOOL(name, outVar, expr) \
  do { \
    uint32_t __t0 = millis(); \
    (outVar) = (expr); \
    noteBlock((name), millis() - __t0); \
  } while (0)


// Button feature gate: 0 = disabled, 1 = enabled
#define ENABLE_BUTTON_INPUT 1


// =====================================================
// SCHEDULING (NTP-based)
// =====================================================
int lastWeatherUpdateHour = -1;
int lastForecastUpdateDay = -1;
int lastForecastUpdateSlot = -1;

const int WEATHER_WINDOW_SECONDS = 10;
const int FORECAST_WINDOW_SECONDS = 30;

const int FORECAST_HOUR_1 = 6;
const int FORECAST_HOUR_2 = 18;

void serviceTime() {
  uint32_t now = millis();
  if (now - lastNtpMs >= NTP_SYNC_MS) {
    bool ok = false;
    WRAP_BLOCK_RET_BOOL("timeClient.update", ok, timeClient.update());
    Serial.printf("[NTP] update ok=%d\n", ok);
    lastNtpMs = now;
  }
}


// =====================================================
// SCROLLING (bottom band)
// =====================================================
int scrollX = 0;
int scrollSpeed = 1;
unsigned long lastScrollUpdate = 0;
int scrollInterval = 50;
String scrollingText = "";

const long adInterval = 60000;
unsigned long adPreviousMillis = 0;


// =====================================================
// CITY SCROLL (top band)
// =====================================================
int cityScrollX = 0;
unsigned long lastCityScrollUpdate = 0;
int cityScrollInterval = 160;
bool cityNeedsScroll = false;

const int CITY_Y = 0;
const int CITY_H = 6;
const int CITY_OFFSET_RIGHT = 33;

// Pause control
unsigned long cityPauseMs = 5000;
bool cityPaused = false;
unsigned long cityPauseStart = 0;


// =====================================================
// DEMO MODE (optional)
// =====================================================
uint32_t g_demoHoldUntilMs = 0;
const uint32_t DEMO_HOLD_MS = 5000;

bool g_demoMode = false;

static const char* CITY_CYCLE[] = {
  "Toronto", "Vancouver", "Sydney", "Brisbane", "London",
  "Tokyo", "Paris", "Berlin", "Dubai"
};
static const int CITY_CYCLE_COUNT = sizeof(CITY_CYCLE) / sizeof(CITY_CYCLE[0]);

int g_demoCityIndex = 0;
const uint32_t DEMO_SWITCH_MS = 20000;
uint32_t g_demoNextSwitchMs = 0;

const uint32_t DEMO_FORECAST_EVERY_MS = 120000;
uint32_t g_demoNextForecastMs = 0;

String g_userCityBackup = "";


// =====================================================
// SLEEP / NIGHT MODE (runtime + WiFiManager)
// =====================================================
char sleepEnabledBuf[2] = "1";
char sleepStartBuf[3] = "3";  //CHANGE
char sleepEndBuf[3] = "4";

WiFiManagerParameter p_sleepEnabled("sleepEnabled", "Sleep enabled? (1=on,0=off)", sleepEnabledBuf, 2);
WiFiManagerParameter p_sleepStart("sleepStart", "Sleep start hour (0-23)", sleepStartBuf, 3);
WiFiManagerParameter p_sleepEnd("sleepEnd", "Sleep end hour (0-23)", sleepEndBuf, 3);

bool g_sleepEnabled = true;
int g_sleepStartHour = 1;  // Runtime default (testing)
int g_sleepEndHour = 2;


// =====================================================
// UPDATE INTERVALS (WiFiManager + runtime)
// =====================================================
int g_weatherUpdateMins = 60;  // Weather refresh
int g_checkinUpdateMins = 60;  // Animation check-in refresh


// =====================================================
// MODE DISPLAY DURATIONS (seconds) - WiFiManager + runtime
// =====================================================
int g_weatherModeSeconds = 30;  // Weather screen duration in UI_WEATHER cycle
int g_animModeSeconds = 10;     // Animation duration in UI_WEATHER cycle
int g_clockModeSeconds = 10;    // Timed clock mode duration

char weatherModeSecsBuf[6] = "30";
char animModeSecsBuf[6] = "10";
char clockModeSecsBuf[6] = "10";

WiFiManagerParameter p_weatherModeSecs("wModeSecs", "Weather screen seconds (e.g., 30)", weatherModeSecsBuf, 6);
WiFiManagerParameter p_animModeSecs("aModeSecs", "Animation seconds (e.g., 10)", animModeSecsBuf, 6);
WiFiManagerParameter p_clockModeSecs("cModeSecs", "Clock mode seconds (e.g., 10)", clockModeSecsBuf, 6);


// =====================================================
// AD ANIMATION DURATION (seconds) - WiFiManager + runtime
// =====================================================
int g_adAnimSeconds = 10;     // Runtime default
char adAnimSecBuf[6] = "10";  // Portal buffer

WiFiManagerParameter p_adAnimSecs(
  "adSecs",
  "Ad animation seconds (e.g., 10)",
  adAnimSecBuf,
  6);


// WiFiManager update interval buffers
char weatherUpdateBuf[5] = "60";  // Up to 9999
char checkinUpdateBuf[5] = "60";  // Up to 9999

WiFiManagerParameter p_weatherUpdateMins(
  "wxMins",
  "Weather update interval (minutes)",
  weatherUpdateBuf,
  5);

WiFiManagerParameter p_checkinUpdateMins(
  "chkMins",
  "Animation update check (minutes)",
  checkinUpdateBuf,
  5);

// Info/help block in portal
WiFiManagerParameter p_updateInfo(
  "<div style='font-family:Arial; font-size:14px; padding:10px; border:1px solid #bbb;'"
  "border-radius:8px; background:#f7f7f7; margin:10px 0;'>"
  "<b>Update Timers</b><br>"
  "<b>Weather update interval</b>: how often the device refreshes current weather.<br>"
  "<b>Animation update check</b>: how often it calls the server to see if a new .bin is available.<br><br>"
  "Recommended: Weather = <code>60</code> minutes, Animation check = <code>60</code> minutes."
  "</div>");

// Loop timers
// Loop timers
static uint32_t g_lastWeatherUpdateMs = 0;
static uint32_t g_lastCheckinMs = 0;

// Manual trigger anti-spam
static uint32_t g_lastManualCheckinMs = 0;


// =====================================================
// BRIGHTNESS (WiFiManager + runtime)
// =====================================================
char brightnessBuf[2] = "3";
int g_brightnessLevel = 3;
WiFiManagerParameter p_brightness("brightness", "Brightness (1-5) default 3", brightnessBuf, 2);


// =====================================================
// WiFiManager CITY + ANIM TAG PARAMETERS
// =====================================================
WiFiManagerParameter custom_parameter("City", "Enter your City for Weather.", "", 20);

// Tag
char animTagBuf[17] = "";
WiFiManagerParameter p_animTag("animTag", "Animation Tag (e.g., ABCD123)", animTagBuf, 17);

// Runtime tag variable
//Ryu01
String g_animTag = "Testtl";


// URL encoder helper
static String urlEncode(const String& s) {
  String out;
  const char* hex = "0123456789ABCDEF";
  for (size_t i = 0; i < s.length(); i++) {
    uint8_t c = (uint8_t)s[i];
    // Unreserved: A-Z a-z 0-9 - _ . ~
    bool ok =
      (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '-' || c == '_' || c == '.' || c == '~';
    if (ok) out += (char)c;
    else {
      out += '%';
      out += hex[(c >> 4) & 0xF];
      out += hex[c & 0xF];
    }
  }
  return out;
}
static String stripTrailingSlashes(String s) {
  s.trim();
  while (s.endsWith("/")) s.remove(s.length() - 1);
  return s;
}

static String buildWeatherEndpoint(const String& pathNoLeadingSlash) {
  String base = stripTrailingSlashes(g_weatherBaseUrl);
  if (base.length() == 0) base = "https://api.openweathermap.org/data/2.5";
  return base + "/" + pathNoLeadingSlash;  // e.g. .../weather
}

static String buildCheckinUrl() {
  String base = stripTrailingSlashes(g_checkinBaseUrl);
  if (base.length() == 0) base = "https://www.auroradisplay.ca";
  return base + "/api/checkin";
}


// =====================================================
// WiFiManager HTML blocks / helper links
// =====================================================
WiFiManagerParameter p_instructions(
  "<div style='font-family:Arial; font-size:14px; padding:10px; border:1px solid #bbb;'"
  "border-radius:8px; background:#f7f7f7; margin:10px 0;'>"
  "<b>City Name Rule (Important)</b><br>"
  "Before you type your city here, test it on:<br>"
  "<a href='https://openweathermap.org/' target='_blank'>openweathermap.org</a><br><br>"

  "Use the exact spelling that appears as the <b>first</b> search result."
  "</div>");

WiFiManagerParameter p_sleepInfo(
  "<div style='font-family:Arial; font-size:14px; padding:10px; border:1px solid #bbb;'"
  "border-radius:8px; background:#f7f7f7; margin:10px 0;'>"
  "<b>Sleep / Night Mode</b><br>"
  "<b>sleepEnabled</b>: enter <code>1</code> for ON, <code>0</code> for OFF.<br><br>"
  "<b>If sleepEnabled = 0</b>: the display stays on all the time and <b>sleepStart/sleepEnd are ignored</b>.<br><br>"
  "<b>What Sleep Mode does:</b><br>"
  "• turns off the weather/scroll display<br>"
  "• shows a simple clock only<br>"
  "• lowers brightness to reduce glare at night"
  "</div>");

WiFiManagerParameter p_brightnessInfo(
  "<div style='font-family:Arial; font-size:14px; padding:10px; border:1px solid #bbb;'"
  "border-radius:8px; background:#f7f7f7; margin:10px 0;'>"
  "<b>Brightness</b><br>"
  "Enter a value from <code>1</code> (dim) to <code>5</code> (bright). Default is <b>3</b>."
  "</div>");

WiFiManagerParameter p_helpLink(
  "helpLink",
  "<div style='margin:8px 0;'>"
  "<a href='/help' style='display:inline-block; padding:10px 14px; border-radius:8px; "
  "background:#222; color:#fff; text-decoration:none; font-weight:bold;'>"
  "City Test / Help</a></div>");


// =====================================================
// FORWARD DECLARATIONS (grouped)
// =====================================================
//




// =====================================================
// DEVICE-INITIATED CHECK-IN TRIGGERS (manual calls)
// Paste this in your FORWARD DECLARATIONS section
// =====================================================

// One-shot check-in you can call from anywhere (button, serial command, etc)
bool deviceCheckinNow(bool quiet, const char* reason = "manual");

// Legacy alias used by button handler
bool doManualCheckin(bool quiet = true);


// Optional: show quick result overlay without breaking your main UI
void deviceShowCheckinResultOverlay(bool ok,
                                    int httpCode,
                                    long rttMs,
                                    uint32_t ms = 1800);

// Optional: simple rate limiter for manual triggers (prevents accidental double-press spam)
bool deviceCheckinAllowedNow(uint32_t nowMs, uint32_t minGapMs = 5000);



// Note: retained as-is for safety. Removing these without scanning the full
// compilation unit can change build behavior in Arduino/C++.
//

bool loadTimelineDurationsFromJson(const String& jsonPath, int frameCountExpected);
void applyDefaultDurations(int frameCount, uint16_t ms = TL_DEFAULT_MS);
static void normalizeDurationsToFrameCount(int frameCountExpected);
static bool deriveDurationsFromItems(JsonVariantConst items, int frameCountExpected);



void applyWifiCustomParams(
  const char* city = nullptr,
  const char* animTag = nullptr,
  const int* brightness = nullptr,
  const bool* sleepEnabled = nullptr,
  const int* sleepStartHour = nullptr,
  const int* sleepEndHour = nullptr,
  const int* weatherUpdateMins = nullptr,
  const int* checkinUpdateMins = nullptr,
  const int* weatherModeSeconds = nullptr,
  const int* animModeSeconds = nullptr,
  const int* clockModeSeconds = nullptr,
  const int* adAnimSeconds = nullptr,
  const char* weatherBaseUrl = nullptr,
  const char* checkinBaseUrl = nullptr,
  bool applyNow = true);



static inline bool canDoNetworkNow(uint32_t now);

// UI mode helpers
static void flashMode();
static void cycleUiMode();

// Tiny helpers
static inline void qDelay(bool quiet, uint32_t ms);

// Backend sync + check-in
bool checkInAndUpdateFromServer(const String& checkinUrl, bool quiet);

// Init / hardware
void setupDisplay();
void setupButtonGPIO();

// 3x5 font / drawing primitives
void drawCharWithCustomFont(int16_t x, int16_t y, char c, uint16_t color, uint16_t bgcolor);
void drawString3x5(int x, int y, const String& s, uint16_t color, uint16_t bg);
void drawCentered3x5(int y, const String& s, uint16_t color, uint16_t bg);
int textWidth3x5(const String& s);
int textWidth3x5(const String& s, int spacing);

// Highlight helper
int textWidthPx3x5(const String& s);
static bool splitHighlight(const String& s, String& pre, String& hi, String& post);
static void drawCentered3x5WithHighlight(int y, const String& s, uint16_t fg, uint16_t hiColor, uint16_t bg);

// Status / UI pages
void showStatusScreen(const String& title,
                      const String& line1 = "",
                      const String& line2 = "",
                      const String& line3 = "",
                      uint16_t fg = 0,
                      uint16_t bg = 0);

void drawFetchStatus3x5(const String& what);
String nowHHMMSS();

// Icons
void drawIconDirectly(const uint16_t* icon, int xPos, int yPos);
void drawIconWithVariableSize(const uint16_t* icon, int xPos, int yPos, int width, int height);

// Clock
void drawDigitalClock();

// Weather (HTTP + parse + render)
String fetchWeather();
String fetchForecast();
String updateWeatherForecast();
void fetchAndStoreWeatherData(const String& jsonPayload);
bool updateWeatherDisplay();
bool updateForecastAndStore();
void drawWeatherDataAndClock();

// Scrolling
void updateScrollingText();
void drawScrollingText(int x, int y, String text, uint16_t color, uint16_t bgcolor);
int calculateTextWidth(String text);

// City band
void initCityScroll(const String& city);
void updateCityScrollBand(const String& cityIn);
int cityTextWidth(const String& text);

// Config (LittleFS JSON)
void saveConfig();
bool loadConfig();
void saveConfigCallback();

// Button + reset
static inline bool buttonPressedNow();
void checkButton(WiFiManager& wm);
void showButton1sMessage();
void serviceButtonAnytime(uint32_t now);

// Hold UI pages
bool serviceButtonHoldUI(uint32_t now);
static void drawHoldPageNumber(uint8_t page);
static void renderHoldPage1();
static void renderHoldPage2();
static void renderHoldPage3();

// Parsing / clamp helpers
int clampHour(int v);
int clamp15(int v);
int clampMins(int v, int minV, int maxV);
bool parseBool01(const char* s, bool defVal);
int parseIntOrDefault(const char* s, int defVal);
bool isValidTagChar(char c);
bool isInOnWindow(int hour, bool enabled, int sleepStart, int sleepEnd);

// Brightness
uint8_t brightnessToPWM(int level);
void applyBrightness();

// Date helpers
int getLocalDayOfMonth();
String getDayOfWeek(long timestamp);

// Demo mode
void demoSetCityAndFetch(const char* city);
void handleDemoMode();

// LittleFS info
void printFSInfo();

// HWID splash
String getHardwareIdString();
void showHardwareIdSplash(uint32_t ms = 3000);

// Tag / paths
String cleanTagFromString(const String& raw);
void applyTagAndPaths(const String& rawTag);

// Animation player (LittleFS BIN)
struct FSAnimPlayer;  // Forward declaration
static bool readFrameFromOpenFile(FSAnimPlayer& p, int frameIndex, uint16_t* outBuf);
static bool readNextFrameFromOpenFile(FSAnimPlayer& p, uint16_t* outBuf);

int getFrameCountFromFS(const String& path);

void drawFrame64x32_RAM(const uint16_t* frame, int xPos, int yPos);
void startAnim(FSAnimPlayer& p);
void stopAnim(FSAnimPlayer& p);
void updateAnim(FSAnimPlayer& p);

// Download / atomic swap
static bool downloadToTempFile(const String& url,
                               const String& finalPath,
                               size_t expectedSize,
                               uint32_t timeoutMs = 15000,
                               bool secureOverride = true,
                               const String& uiCode = "");

static void cleanupStaleTemp(const String& finalPath);
static bool commitTempFile(const String& finalPath);
static void recoverTempAndBackup(const String& finalPath);
void drawBinDownloadProgress3x5(const String& code, int pct, size_t done, size_t total);

// Backend sync + check-in
bool syncSettingsFromBackendAndOverwriteWiFi(const String& url);




void applyDefaultDurations(int frameCount, uint16_t ms) {
  if (frameCount < 0) frameCount = 0;
  if (frameCount > TL_MAX_FRAMES) frameCount = TL_MAX_FRAMES;

  g_timelineCount = frameCount;
  for (int i = 0; i < g_timelineCount; i++) g_timelineDurMs[i] = tlClampMs(ms);
  g_timelineLoaded = (g_timelineCount > 0);
}

static void normalizeDurationsToFrameCount(int frameCountExpected) {
  if (frameCountExpected < 0) frameCountExpected = 0;
  if (frameCountExpected > TL_MAX_FRAMES) frameCountExpected = TL_MAX_FRAMES;

  if (g_timelineCount <= 0) {
    applyDefaultDurations(frameCountExpected, TL_DEFAULT_MS);
    return;
  }

  if (g_timelineCount < frameCountExpected) {
    uint16_t pad = g_timelineDurMs[g_timelineCount - 1];
    for (int i = g_timelineCount; i < frameCountExpected; i++) g_timelineDurMs[i] = pad;
    g_timelineCount = frameCountExpected;
  } else if (g_timelineCount > frameCountExpected) {
    g_timelineCount = frameCountExpected;
  }
}

static bool deriveDurationsFromItems(JsonVariantConst items, int frameCountExpected) {
  g_timelineCount = 0;

  if (!items.is<JsonArrayConst>()) return false;
  JsonArrayConst arr = items.as<JsonArrayConst>();

  for (JsonObjectConst card : arr) {
    const char* t = card["type"] | "";
    int dur = card["durationMs"] | 5000;
    if (dur < 1) dur = 1;

    if (strcmp(t, "color") == 0 || strcmp(t, "image") == 0 || strcmp(t, "text") == 0) {
      if (g_timelineCount < TL_MAX_FRAMES) {
        g_timelineDurMs[g_timelineCount++] = tlClampMs(dur);
      }
    } else if (strcmp(t, "transition") == 0) {
      int steps = card["steps"] | 10;
      if (steps < 1) steps = 1;
      int per = dur / steps;
      if (per < 1) per = 1;

      for (int i = 0; i < steps; i++) {
        if (g_timelineCount < TL_MAX_FRAMES) {
          g_timelineDurMs[g_timelineCount++] = tlClampMs(per);
        }
      }
    }
  }

  normalizeDurationsToFrameCount(frameCountExpected);
  return (g_timelineCount > 0);
}

static bool loadDurationsFromArrayMs(JsonVariantConst arrVar, int frameCountExpected, const char* label) {
  if (!arrVar.is<JsonArrayConst>()) return false;

  JsonArrayConst arr = arrVar.as<JsonArrayConst>();
  g_timelineCount = 0;

  for (JsonVariantConst v : arr) {
    if (g_timelineCount >= TL_MAX_FRAMES) break;

    // Accept numbers or numeric strings
    int d = 0;
    if (v.is<int>() || v.is<long>() || v.is<float>() || v.is<double>()) {
      d = (int)round(v.as<float>());
    } else if (v.is<const char*>()) {
      d = atoi(v.as<const char*>());
    } else {
      continue;
    }

    g_timelineDurMs[g_timelineCount++] = tlClampMs(d);
  }

  normalizeDurationsToFrameCount(frameCountExpected);
  g_timelineLoaded = (g_timelineCount > 0);

  if (g_timelineLoaded) {
    Serial.printf("[TL] Loaded %s: raw=%d normalized=%d first=%u last=%u\n",
                  label,
                  (int)arr.size(),
                  g_timelineCount,
                  (unsigned)g_timelineDurMs[0],
                  (unsigned)g_timelineDurMs[g_timelineCount - 1]);
  }
  return g_timelineLoaded;
}

static bool loadDurationsFromArraySeconds(JsonVariantConst arrVar, int frameCountExpected, const char* label) {
  if (!arrVar.is<JsonArrayConst>()) return false;

  JsonArrayConst arr = arrVar.as<JsonArrayConst>();
  g_timelineCount = 0;

  for (JsonVariantConst v : arr) {
    if (g_timelineCount >= TL_MAX_FRAMES) break;

    float s = 0.0f;
    if (v.is<int>() || v.is<long>() || v.is<float>() || v.is<double>()) {
      s = v.as<float>();
    } else if (v.is<const char*>()) {
      s = atof(v.as<const char*>());
    } else {
      continue;
    }

    int d = (int)roundf(s * 1000.0f);
    g_timelineDurMs[g_timelineCount++] = tlClampMs(d);
  }

  normalizeDurationsToFrameCount(frameCountExpected);
  g_timelineLoaded = (g_timelineCount > 0);

  if (g_timelineLoaded) {
    Serial.printf("[TL] Loaded %s (sec->ms): raw=%d normalized=%d first=%u last=%u\n",
                  label,
                  (int)arr.size(),
                  g_timelineCount,
                  (unsigned)g_timelineDurMs[0],
                  (unsigned)g_timelineDurMs[g_timelineCount - 1]);
  }
  return g_timelineLoaded;
}




bool loadTimelineDurationsFromJson(const String& jsonPath, int frameCountExpected) {
  g_timelineLoaded = false;
  g_timelineCount = 0;

  if (frameCountExpected <= 0) {
    Serial.println("[TL] frameCountExpected <= 0");
    return false;
  }

  File f = LittleFS.open(jsonPath, "r");
  if (!f) {
    Serial.printf("[TL] Missing JSON: %s\n", jsonPath.c_str());
    applyDefaultDurations(frameCountExpected, TL_DEFAULT_MS);
    return false;
  }

  size_t sz = f.size();
  if (sz == 0 || sz > 128 * 1024) {
    Serial.printf("[TL] Invalid JSON size: %u\n", (unsigned)sz);
    f.close();
    applyDefaultDurations(frameCountExpected, TL_DEFAULT_MS);
    return false;
  }

  std::unique_ptr<char[]> buf(new char[sz + 1]);
  size_t got = f.readBytes(buf.get(), sz);
  f.close();
  buf[got] = '\0';

  DynamicJsonDocument doc(64 * 1024);
  DeserializationError err = deserializeJson(doc, buf.get(), got);
  if (err) {
    Serial.printf("[TL] JSON parse failed: %s\n", err.c_str());
    applyDefaultDurations(frameCountExpected, TL_DEFAULT_MS);
    return false;
  }

  // 1) direct ms arrays (common)
  if (loadDurationsFromArrayMs(doc["durations_ms"], frameCountExpected, "durations_ms")) return true;
  if (loadDurationsFromArrayMs(doc["frame_durations_ms"], frameCountExpected, "frame_durations_ms")) return true;
  if (loadDurationsFromArrayMs(doc["timeline"]["durations_ms"], frameCountExpected, "timeline.durations_ms")) return true;

  // 2) seconds arrays -> convert to ms
  if (loadDurationsFromArraySeconds(doc["durations"], frameCountExpected, "durations")) return true;
  if (loadDurationsFromArraySeconds(doc["timeline"]["durations"], frameCountExpected, "timeline.durations")) return true;

  // 3) frames[] objects with duration fields
  JsonVariantConst frames = doc["frames"];
  if (!frames.is<JsonArrayConst>()) frames = doc["timeline"]["frames"];
  if (frames.is<JsonArrayConst>()) {
    g_timelineCount = 0;
    for (JsonObjectConst fr : frames.as<JsonArrayConst>()) {
      if (g_timelineCount >= TL_MAX_FRAMES) break;

      // Prefer explicit ms
      int dMs = fr["durationMs"] | fr["duration_ms"] | -1;

      if (dMs < 0) {
        // maybe seconds field
        if (!fr["duration"].isNull()) {
          float s = fr["duration"].as<float>();
          dMs = (int)roundf(s * 1000.0f);
        }
      }

      if (dMs < 0) dMs = TL_DEFAULT_MS;
      g_timelineDurMs[g_timelineCount++] = tlClampMs(dMs);
    }

    normalizeDurationsToFrameCount(frameCountExpected);
    g_timelineLoaded = (g_timelineCount > 0);
    if (g_timelineLoaded) {
      Serial.printf("[TL] Loaded from frames[]: normalized=%d first=%u last=%u\n",
                    g_timelineCount,
                    (unsigned)g_timelineDurMs[0],
                    (unsigned)g_timelineDurMs[g_timelineCount - 1]);
      return true;
    }
  }

  // 4) existing fallback from items[]
  bool ok = deriveDurationsFromItems(doc["items"], frameCountExpected);
  g_timelineLoaded = ok;
  if (ok) {
    Serial.printf("[TL] Derived from items, entries=%d\n", g_timelineCount);
    return true;
  }

  applyDefaultDurations(frameCountExpected, TL_DEFAULT_MS);
  Serial.println("[TL] No known timeline format found, default timings applied");
  return false;
}




// =====================================================
// ANIMATION PLAYER (LittleFS BIN frames)
// =====================================================
struct FSAnimPlayer {
  bool playing = false;
  uint32_t startMs = 0;
  uint32_t lastFrameMs = 0;
  int frameIndex = 0;

  uint32_t showDurationMs = 8000;
  uint32_t frameDelayMs = 60;

  String path = "/ryu.bin";
  int frameCount = 0;

  // Keep file open for faster frame reads
  File file;
  bool fileOpen = false;
};

static bool readFrameFromOpenFile(FSAnimPlayer& p, int frameIndex, uint16_t* outBuf) {
  if (!p.fileOpen) return false;

  const size_t frameBytes = 64 * 32 * 2;
  const size_t offset = (size_t)frameIndex * frameBytes;

  if (!p.file.seek(offset, SeekSet)) return false;

  // Read full frame in one pass; bytes are little-endian RGB565
  size_t got = p.file.readBytes((char*)outBuf, frameBytes);
  return (got == frameBytes);
}


// =====================================================
// TAG -> PATHS (LittleFS filenames) + validation
// =====================================================
String g_tag = "";
String g_tagConfigPath = "";
String g_tagJsonPath = "";
String g_animBinPath = "";

String cleanTagFromString(const String& raw) {
  String s = raw;
  s.trim();

  String out = "";
  for (size_t i = 0; i < s.length(); i++) {
    char c = s[i];
    if (isValidTagChar(c)) out += c;
  }

  // Case-sensitive by design
  if (out.length() < 1) return "";
  if (out.length() > 10) out = out.substring(0, 10);
  return out;
}

FSAnimPlayer adAnim;

// Shared frame buffer
static uint16_t frameBuf[64 * 32];

void applyTagAndPaths(const String& rawTag) {
  g_tag = cleanTagFromString(rawTag);

  if (g_tag.length() == 0) {
    g_tagConfigPath = "/config.json";
    g_tagJsonPath = "/display.json";
    g_animBinPath = "/ryu.bin";
  } else {
    g_tagConfigPath = "/" + g_tag + ".config";
    g_tagJsonPath = "/" + g_tag + ".json";
    g_animBinPath = "/" + g_tag + ".bin";
  }

  // Player points to /<TAG>.bin
  adAnim.path = g_animBinPath;

  g_animTag = g_tag;
  g_animMissing = false;
  g_animMissingUiMs = 0;
  g_animMissingLogMs = 0;
}

static bool readNextFrameFromOpenFile(FSAnimPlayer& p, uint16_t* outBuf) {
  if (!p.fileOpen) return false;

  const size_t frameBytes = 64 * 32 * 2;
  const size_t fileSize = p.file.size();

  // Need at least one full frame
  if (fileSize < frameBytes) return false;

  // Wrap to start if next frame would exceed EOF
  size_t pos = p.file.position();
  if (pos + frameBytes > fileSize) {
    if (!p.file.seek(0, SeekSet)) return false;
  }

  // Read one full frame (little-endian RGB565)
  size_t got = p.file.readBytes((char*)outBuf, frameBytes);
  if (got != frameBytes) return false;

  return true;
}


// =====================================================
// DEBUG DIAGNOSTICS
// =====================================================
int lastWeatherHttpCode = 0;
int lastForecastHttpCode = 0;

uint32_t lastWeatherFetchMs = 0;
uint32_t lastForecastFetchMs = 0;

// Check-in diagnostics
int g_lastCheckinHttpCode = 0;
uint32_t g_lastCheckinRttMs = 0;
uint32_t g_loopMaxMs = 0;


// =====================================================
// SMALL HELPERS
// =====================================================
static inline bool canDoNetworkNow(uint32_t now) {
  // Skip network on this pass if loop already stalling
  if (g_loopMaxMs > 250) return false;
  if ((int32_t)(now - g_netBackoffUntilMs) < 0) return false;
  return true;
}

// Quiet-mode delay:
// - quiet=false: preserves debug pacing delays
// - quiet=true: removes delays
static inline void qDelay(bool quiet, uint32_t ms) {
  if (!quiet) delay(ms);
}

static inline bool buttonPressedNow() {
#if ENABLE_BUTTON_INPUT
  return (digitalRead(BTN_PIN) == LOW);
#else
  return false;
#endif
}

void setupButtonGPIO() {
#if ENABLE_BUTTON_INPUT
  pinMode(BTN_PIN, INPUT_PULLUP);
#endif
}

int clampHour(int v) {
  if (v < 0) return 0;
  if (v > 23) return 23;
  return v;
}

int clamp15(int v) {
  if (v < 1) return 1;
  if (v > 5) return 5;
  return v;
}

int clampMins(int v, int minV, int maxV) {
  if (v < minV) return minV;
  if (v > maxV) return maxV;
  return v;
}

bool parseBool01(const char* s, bool defVal) {
  if (!s || !*s) return defVal;
  return (s[0] == '1');
}

int parseIntOrDefault(const char* s, int defVal) {
  if (!s || !*s) return defVal;
  return atoi(s);
}

bool isValidTagChar(char c) {
  return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || (c == '-') || (c == '_');
}

bool isInOnWindow(int hour, bool enabled, int sleepStart, int sleepEnd) {
  if (!enabled) return true;
  if (sleepStart == sleepEnd) return true;

  bool inSleep;
  if (sleepStart < sleepEnd) {
    inSleep = (hour >= sleepStart && hour < sleepEnd);
  } else {
    inSleep = (hour >= sleepStart || hour < sleepEnd);
  }
  return !inSleep;
}

uint8_t brightnessToPWM(int level) {
  level = clamp15(level);
  const uint8_t map5[5] = { 24, 48, 80, 120, 170 };
  return map5[level - 1];
}

void applyBrightness() {
  if (!dma_display) return;
  dma_display->setBrightness(brightnessToPWM(g_brightnessLevel));
}

int getLocalDayOfMonth() {
  time_t localEpoch = (time_t)timeClient.getEpochTime();  // already includes OpenWeather offset
  struct tm* ti = gmtime(&localEpoch);                    // do NOT use localtime here
  return ti ? ti->tm_mday : -1;
}


int textWidthPx3x5(const String& s) {
  int n = s.length();
  if (n <= 0) return 0;
  return (n * 4) - 1;  // Last char has no trailing spacing
}

static bool splitHighlight(const String& s, String& pre, String& hi, String& post) {
  int a = s.indexOf("{{");
  int b = s.indexOf("}}");
  if (a < 0 || b < 0 || b <= a + 2) return false;

  pre = s.substring(0, a);
  hi = s.substring(a + 2, b);
  post = s.substring(b + 2);
  return true;
}

static void drawCentered3x5WithHighlight(
  int y,
  const String& s,
  uint16_t fg,
  uint16_t hiColor,
  uint16_t bg) {
  String pre, hi, post;
  if (!splitHighlight(s, pre, hi, post)) {
    drawCentered3x5(y, s, fg, bg);
    return;
  }

  int wPre = pre.length() * 4;
  int wHi = hi.length() * 4;
  int wPost = post.length() * 4;
  int totalW = wPre + wHi + wPost;

  int x = (PANEL_RES_X - totalW) / 2;
  if (x < 0) x = 0;

  if (pre.length()) {
    drawString3x5(x, y, pre, fg, bg);
    x += wPre;
  }
  if (hi.length()) {
    drawString3x5(x, y, hi, hiColor, bg);
    x += wHi;
  }
  if (post.length()) {
    drawString3x5(x, y, post, fg, bg);
  }
}


// Helper: show "no animation" message
static void showNoAnimMessage() {
  uint32_t now = millis();
  if ((int32_t)(now - g_animMissingUiMs) < 2000) return;  // Rate limit
  g_animMissingUiMs = now;

  showStatusScreen("Tag:", "{{" + g_animTag + "}}", "Invalid");

  // Freeze weather scrollers while message is visible
  g_btnOverlayActive = true;
  g_btnNeedsFullRedraw = true;

  // Hold overlay
  g_btnMsgUntilMs = now + 4000;

  // Ensure weather screen gets restored after overlay
  g_animMissingShowUntilMs = now + 4000;
  g_animMissingNeedsRestore = true;
}


// =====================================================
// 3x5 TEXT HELPERS
// =====================================================
int textWidth3x5(const String& s, int spacing) {
  return s.length() * spacing;
}

int textWidth3x5(const String& s) {
  return s.length() * 4;
}

void drawString3x5(int x, int y, const String& s, uint16_t color, uint16_t bg) {
  for (uint16_t i = 0; i < s.length(); i++) {
    drawCharWithCustomFont(x + (i * 4), y, s[i], color, bg);
  }
}

void drawCentered3x5(int y, const String& s, uint16_t color, uint16_t bg) {
  int w = s.length() * 4;
  int x = (PANEL_RES_X - w) / 2;
  if (x < 0) x = 0;
  drawString3x5(x, y, s, color, bg);
}


// =====================================================
// STATUS SCREENS
// =====================================================
void showStatusScreen(
  const String& title,
  const String& line1,
  const String& line2,
  const String& line3,
  uint16_t fg,
  uint16_t bg) {
  if (!dma_display) return;

  if (fg == 0) fg = dma_display->color565(255, 255, 255);
  if (bg == 0) bg = dma_display->color565(0, 0, 0);

  dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, bg);

  drawCentered3x5(0, title, fg, bg);

  if (line1.length()) drawCentered3x5WithHighlight(9, line1, fg, UI_YELLOW, bg);
  if (line2.length()) drawCentered3x5WithHighlight(16, line2, fg, UI_YELLOW, bg);
  if (line3.length()) drawCentered3x5WithHighlight(23, line3, fg, UI_YELLOW, bg);
}


// =====================================================
// FETCH STATUS
// =====================================================
String nowHHMMSS() {
  return timeClient.getFormattedTime();
}

void drawFetchStatus3x5(const String& what) {
  dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, UI_BLACK);

  drawCentered3x5(0, "FETCH", UI_WHITE, UI_BLACK);
  drawCentered3x5(7, what, UI_WHITE, UI_BLACK);
  drawCentered3x5(14, "TRY", UI_WHITE, UI_BLACK);
  drawCentered3x5(21, nowHHMMSS(), UI_WHITE, UI_BLACK);
}


// =====================================================
// LITTLEFS INFO
// =====================================================
void printFSInfo() {
  size_t total = LittleFS.totalBytes();
  size_t used = LittleFS.usedBytes();
  size_t freeB = (total > used) ? (total - used) : 0;
  Serial.printf("LittleFS total=%u used=%u free=%u bytes\n",
                (unsigned)total, (unsigned)used, (unsigned)freeB);
}


// =====================================================
// DOWNLOAD UI (progress bar)
// =====================================================
void drawBinDownloadProgress3x5(const String& code, int pct, size_t done, size_t total) {
  if (!dma_display) return;

  dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, UI_BLACK);

  showStatusScreen("FETCH", "CODE:{{" + code + "}}");

  String pctLine;
  if (pct >= 0) pctLine = "DL " + String(pct) + "%";
  else pctLine = "DL " + String((unsigned)done);

  drawCentered3x5(21, pctLine, UI_WHITE, UI_BLACK);

  // Progress bar (bottom row)
  int barX = 2;
  int barY = 28;
  int barW = PANEL_RES_X - 4;
  int barH = 3;

  dma_display->drawRect(barX, barY, barW, barH, UI_WHITE);

  if (pct >= 0) {
    int fillW = (barW - 2) * pct / 100;
    if (fillW < 0) fillW = 0;
    if (fillW > (barW - 2)) fillW = barW - 2;
    dma_display->fillRect(barX + 1, barY + 1, fillW, barH - 2, UI_BLUE);
  }
}


// =====================================================
// HOLD UI PAGES (2-30s while pressed)
// =====================================================
static void drawHoldPageNumber(uint8_t page) {
  int x = PANEL_RES_X - 4;  // 1 character width (4px including spacing)
  int y = 0;

  dma_display->fillRect(x, y, 4, 6, UI_BLACK);
  drawString3x5(x, y, String(page), UI_YELLOW, UI_BLACK);
}

static void renderHoldPage1() {
  String ssid = (WiFi.status() == WL_CONNECTED) ? WiFi.SSID() : String("DISCONNECTED");
  int rssi = (WiFi.status() == WL_CONNECTED) ? WiFi.RSSI() : 0;

  String hwid = getHardwareIdString();
  if (ssid.length() > 16) ssid = ssid.substring(0, 16);

  showStatusScreen(
    "WIFI",
    "SSID:{{" + ssid + "}}",
    (WiFi.status() == WL_CONNECTED) ? ("RSSI:{{" + String(rssi) + "}}") : "RSSI:{{N/A}}",
    "HW:{{" + hwid + "}}");

  drawHoldPageNumber(1);
}

static void renderHoldPage2() {
  String tag = g_animTag;
  tag.trim();
  if (tag.length() == 0) tag = "NOT SET";
  if (tag.length() > 16) tag = tag.substring(0, 16);

  String city = weatherCity;
  city.trim();
  if (city.length() == 0) city = globalCityName;
  city.trim();
  if (city.length() == 0) city = "NOT SET";
  if (city.length() > 16) city = city.substring(0, 16);

  showStatusScreen(
    "INFO",
    "TAG:{{" + tag + "}}",
    "CITY:{{" + city + "}}",
    "");

  drawHoldPageNumber(2);
}

static void renderHoldPage3() {
  showStatusScreen(
    "BRIGHT",
    "LEVEL:{{" + String(g_brightnessLevel) + "/5}}",
    "",
    "");
  drawHoldPageNumber(3);
}

void deviceShowCheckinResultOverlay(bool ok, int httpCode, long rttMs, unsigned long ms) {
  (void)httpCode;
  (void)rttMs;

  if (ok && ms > 0) {
    g_btnMsgUntilMs = millis() + ms;
    g_btnOverlayActive = true;
    g_btnNeedsFullRedraw = true;

    enterPairFlowWaitCode();
    return;
  }

  if (ok) showStatusScreen("CHECKIN OK", "NO UPDATE", " ", " ");
  else showStatusScreen("CHECKIN FAIL", " ", " ", "TRY AGAIN");

  g_btnMsgUntilMs = millis() + ms;
  g_btnOverlayActive = (ms > 0);
  if (g_btnOverlayActive) g_btnNeedsFullRedraw = true;
}

void deviceShowCheckinResultOverlay_OLD(bool ok, int httpCode, uint32_t rttMs, uint32_t ms) {
  if (!dma_display) return;

  if (ok) {
    if (g_lastCheckinHadPairing) {
      // Success + pairing code
      showStatusScreen(
        "PAIR READY",
        "CODE:" + g_lastPairCode,
        "ENTER ON WEB",
        "OK");
    } else {
      // Success but no pairing code returned
      showStatusScreen(
        "CHECKIN OK",
        "NO UPDATE",
        "HTTP:" + String(httpCode),
        "RTT:" + String((unsigned long)rttMs) + "MS");
    }
  } else {
    showStatusScreen(
      "CHECKIN FAIL",
      "HTTP:" + String(httpCode),
      "RTT:" + String((unsigned long)rttMs) + "MS",
      "TRY AGAIN");
  }

  g_btnMsgUntilMs = millis() + ms;
  g_btnOverlayActive = true;
  g_btnNeedsFullRedraw = true;
}



bool serviceButtonHoldUI(uint32_t now) {
#if !ENABLE_BUTTON_INPUT
  (void)now;
  return false;
#endif
  bool reading = buttonPressedNow();

  // Debounce
  if (reading != g_btnLastReading) {
    g_btnLastReading = reading;
    g_btnChangeMs = now;
  }

  if (now - g_btnChangeMs > BTN_DEBOUNCE_MS) {
    if (reading != g_btnStablePressed) {
      g_btnStablePressed = reading;

      if (g_btnStablePressed) {
        // Just pressed
        g_btnPressStartMs = now;
        g_holdActive = false;
        g_holdPageShown = 0;
        g_holdLastUiMs = 0;
      } else {
        // Just released
        uint32_t heldMs = now - g_btnPressStartMs;

        if (g_holdActive) {
          g_holdActive = false;
          g_holdPageShown = 0;

          g_btnOverlayActive = true;
          g_btnNeedsFullRedraw = true;
        } else {
          // Short press (<2s): cycle UI mode
          if (heldMs < HOLD_NO_ACTION_MS) {
            cycleUiMode();
          }
        }
      }
    }
  }



  if (!g_btnStablePressed) return false;

  uint32_t heldMs = now - g_btnPressStartMs;
  if (heldMs < HOLD_NO_ACTION_MS) return false;

  uint8_t page = 0;
  if (heldMs < HOLD_PAGE1_END_MS) page = 1;
  else if (heldMs < HOLD_PAGE2_END_MS) page = 2;
  else page = 3;

  g_holdActive = true;

  bool pageChanged = (page != g_holdPageShown);
  bool refresh = pageChanged;

  if (!refresh && page == 1 && (now - g_holdLastUiMs) >= 500) {
    refresh = true;
  }

  if (!refresh) return true;

  g_holdPageShown = page;
  g_holdLastUiMs = now;

  switch (page) {
    case 1: renderHoldPage1(); break;
    case 2: renderHoldPage2(); break;
    case 3: renderHoldPage3(); break;
  }

  return true;
}

// =====================================================
// UI MODE (manual override)
// =====================================================

enum UiMode : uint8_t {
  UI_WEATHER = 0,  // Normal behavior (weather, ads, sleep window)
  UI_CLOCK = 1,    // Clock-only
  UI_ANIM = 2,     // Animation-only (continuous)
  UI_REGDEV = 3    // One-shot: manual check-in / register device
};

static UiMode g_uiMode = UI_WEATHER;
static uint32_t g_regdevConfirmAtMs = 0;  // 0 = no pending action


static void serviceUiModeAnytime(uint32_t now) {
  // Only care about delayed action for Register Device
  if (g_uiMode == UI_REGDEV && g_regdevConfirmAtMs != 0) {
    // Wrap-safe check: has 5s expired?
    if ((int32_t)(now - g_regdevConfirmAtMs) >= 0) {
      g_regdevConfirmAtMs = 0;  // prevent re-trigger

      // Loud manual check-in, shows deviceShowCheckinResultOverlay
      doManualCheckin(false);

      // Treat like returning to normal with fresh timing
      adPreviousMillis = millis();
      screenDrawnOnce = false;
      g_btnOverlayActive = true;
      g_btnNeedsFullRedraw = true;
    }
  }
}




static void flashMode() {
  if (g_uiMode == UI_WEATHER) showStatusScreen("MODE", "WEATHER");
  if (g_uiMode == UI_CLOCK) showStatusScreen("MODE", "CLOCK");
  if (g_uiMode == UI_ANIM) showStatusScreen("MODE", "ALTERNATE");
  if (g_uiMode == UI_REGDEV) showStatusScreen("MODE", "REGISTER DEVICE", "OR", "SERVER CHECKIN");
  //7 second message out of look for checkin for sure
  g_btnMsgUntilMs = millis() + 7000;
}

static void cycleUiMode() {
  uint32_t now = millis();

  // 4 modes now: 0..3
  g_uiMode = (UiMode)((g_uiMode + 1) % 4);

  // Reset timeout by default
  g_uiModeUntilMs = 0;
  g_regdevConfirmAtMs = 0;  // clear any previous pending reg action

  if (g_uiMode == UI_CLOCK) {
    adAnim.playing = false;
    if (g_clockModeTimeoutSeconds > 0) {
      g_uiModeUntilMs = now + (uint32_t)g_clockModeTimeoutSeconds * 1000UL;
    }
  }

  if (g_uiMode == UI_ANIM) {
    startAnim(adAnim);
    if (g_animModeTimeoutSeconds > 0) {
      g_uiModeUntilMs = now + (uint32_t)g_animModeTimeoutSeconds * 1000UL;
    }
  }

  if (g_uiMode == UI_WEATHER) {
    // Back to normal behavior
    if (adAnim.playing) stopAnim(adAnim);  // land on weather, not ad

    // Prevent ad from starting immediately after switch back
    adPreviousMillis = millis();

    // Force a fresh weather draw
    screenDrawnOnce = false;
  }

  if (g_uiMode == UI_REGDEV) {
    // Do NOT register immediately.
    // Start a 5s confirmation window; if user cycles away, we cancel.
    g_regdevConfirmAtMs = now + 5000UL;
  }

  g_btnOverlayActive = true;
  g_btnNeedsFullRedraw = true;
  flashMode();
}


// =====================================================
// CITY BAND HELPERS
// =====================================================
int cityTextWidth(const String& text) {
  return text.length() * 4;
}


























// =====================================================
// DISPLAY INIT (unchanged logic)
// =====================================================
void setupDisplay() {
  HUB75_I2S_CFG::i2s_pins _pins = {
    // R1, G1, B1, R2, G2, B2,  A,  B,  C,  D,  E, LAT, OE, CLK
    25,
    26,
    27,
    14,
    12,
    13,
    23,
    19,
    5,
    17,
    -1,
    4,
    15,
    16,
  };

  int RedGreenSwap = 1;
  if (RedGreenSwap) {
    _pins.r1 = 25;
    _pins.g1 = 27;
    _pins.b1 = 26;
    _pins.r2 = 14;
    _pins.g2 = 13;
    _pins.b2 = 12;
  }

  HUB75_I2S_CFG mxconfig(PANEL_RES_X, PANEL_RES_Y, PANEL_CHAIN, _pins);

  int PixelShift = 1;
  if (PixelShift) {
    mxconfig.clkphase = false;
  }

  dma_display = new MatrixPanel_I2S_DMA(mxconfig);
  dma_display->begin();

  dma_display->setBrightness(0);
  dma_display->clearScreen();
  dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, dma_display->color565(0, 0, 0));
  dma_display->clearScreen();

  UI_WHITE = dma_display->color565(255, 255, 255);
  UI_BLACK = dma_display->color565(0, 0, 0);
  UI_YELLOW = dma_display->color565(253, 253, 150);
  UI_BLUE = dma_display->color565(100, 180, 220);
  UI_RED = dma_display->color565(230, 100, 130);

  dma_display->setTextColor(UI_WHITE);
  dma_display->setBrightness(64);
}


// =====================================================
// ICON DRAWING (unchanged)
// =====================================================
void drawIconDirectly(const uint16_t* icon, int xPos, int yPos) {
  for (int y = 0; y < 25; y++) {
    for (int x = 0; x < 32; x++) {
      int screenX = x + xPos;
      int screenY = y + yPos;
      if (screenX >= 0 && screenX < PANEL_RES_X && screenY >= 0 && screenY < PANEL_RES_Y) {
        uint16_t color = pgm_read_word(&icon[y * 32 + x]);

        uint8_t r = (color >> 11) & 0x1F;
        uint8_t g = (color >> 5) & 0x3F;
        uint8_t b = color & 0x1F;
        r = (r * 255) / 31;
        g = (g * 255) / 63;
        b = (b * 255) / 31;

        dma_display->drawPixelRGB888(screenX, screenY, r, g, b);
      }
    }
  }
}

void drawIconWithVariableSize(const uint16_t* icon, int xPos, int yPos, int width, int height) {
  for (int y = 0; y < height; y++) {
    for (int x = 0; x < width; x++) {
      int screenX = x + xPos;
      int screenY = y + yPos;
      if (screenX >= 0 && screenX < PANEL_RES_X && screenY >= 0 && screenY < PANEL_RES_Y) {
        uint16_t color = pgm_read_word(&icon[y * width + x]);

        uint8_t r = (color >> 11) & 0x1F;
        uint8_t g = (color >> 5) & 0x3F;
        uint8_t b = color & 0x1F;
        r = (r * 255) / 31;
        g = (g * 255) / 63;
        b = (b * 255) / 31;

        dma_display->drawPixelRGB888(screenX, screenY, r, g, b);
      }
    }
  }
}


// =====================================================
// CHAR DRAW (3x5) (unchanged)
// =====================================================
void drawCharWithCustomFont(int16_t x, int16_t y, char c, uint16_t color, uint16_t bgcolor) {
  int charIndex = c - ' ';
  if (charIndex < 0 || charIndex > ('~' - ' ')) return;

  const uint8_t* charBitmap = customFont3x5[charIndex];

  for (int8_t row = 0; row < 5; row++) {
    for (int8_t col = 0; col < 3; col++) {
      if (charBitmap[row] & (1 << (2 - col))) {
        dma_display->drawPixel(x + col, y + row, color);
      } else if (bgcolor != 0xFFFF) {
        dma_display->drawPixel(x + col, y + row, bgcolor);
      }
    }
  }
}


// =====================================================
// CLOCK (unchanged)
// =====================================================
void drawDigitalClock() {
  // Do NOT call timeClient.update() here.
  // Assume something else in your code (loop or a timer) calls timeClient.update() periodically.

  time_t localEpoch = (time_t)timeClient.getEpochTime();
  if (localEpoch == 0) {
    // Time not set yet, nothing to draw
    return;
  }

  // Epoch is already offset by g_tzOffsetSeconds via timeClient.setTimeOffset(...)
  // So treat it as "local" and just break it down.
  struct tm* ti = gmtime(&localEpoch);  // use gmtime, no extra TZ applied
  if (!ti) return;

  int hour = ti->tm_hour;
  int minute = ti->tm_min;

  // 12-hour conversion
  int hour12 = hour % 12;
  if (hour12 == 0) hour12 = 12;

  // "HH:MM", leading space if single digit hour
  char timeBuf[6];  // "HH:MM" + null
  snprintf(timeBuf, sizeof(timeBuf), "%2d:%02d", hour12, minute);

  String displayTime = String(timeBuf);

  uint16_t colorPastelWhite = dma_display->color565(255, 255, 255);
  uint16_t bgColor = dma_display->color565(0, 0, 0);

  int charWidth = 4;                    // your custom font width
  int numChars = displayTime.length();  // should be 5
  int totalWidth = numChars * charWidth;

  int xPosition = dma_display->width() - totalWidth;
  int yPosition = dma_display->height() - 6;

  for (int i = 0; i < numChars; i++) {
    drawCharWithCustomFont(
      xPosition + (i * charWidth),
      yPosition,
      displayTime[i],
      colorPastelWhite,
      bgColor);
  }
}


// =====================================================
// WEATHER HTTP (unchanged)
// =====================================================
// Hardened fetchWeather(): snapshots config, sanitizes fields, validates, and logs WHY failures happen.
// Drop-in replacement for your existing fetchWeather().

static String _wxStripControl(const String& in) {
  String out;
  out.reserve(in.length());
  for (size_t i = 0; i < in.length(); i++) {
    char c = in[i];
    if (c >= 32 && c != 127) out += c;  // remove control chars
  }
  return out;
}

static String _wxSanitize(String s) {
  s = _wxStripControl(s);
  s.trim();
  s.replace("\r", "");
  s.replace("\n", "");
  // remove accidental debug suffixes like "END"
  while (s.endsWith("END")) {
    s.remove(s.length() - 3);
    s.trim();
  }
  return s;
}

static uint32_t _wxFnv1a32(const String& s) {
  uint32_t h = 2166136261u;
  for (size_t i = 0; i < s.length(); i++) {
    h ^= (uint8_t)s[i];
    h *= 16777619u;
  }
  return h;
}

static String _wxRedactKey(const String& key) {
  if (key.length() < 8) return "<redacted>";
  return key.substring(0, 3) + String("***") + key.substring(key.length() - 3);
}

String fetchWeather() {
  Serial.println("\n[WX] ===== fetchWeather() START =====");

  if (netBackoffActive()) {
    Serial.println("[WX] Backoff active, skipping weather fetch");
    return "";
  }

  // Snapshot raw values first so we can see them before sanitize
  String rawEp = buildWeatherEndpoint("weather");
  String rawCity = weatherCity;
  String rawUnit = weatherUnits;
  String rawKey = weatherApiKey;

  Serial.println("[WX][DBG] Raw config before sanitize:");
  Serial.print("  rawEp   = '");
  Serial.print(rawEp);
  Serial.println("'");
  Serial.print("  rawCity = '");
  Serial.print(rawCity);
  Serial.println("'");
  Serial.print("  rawUnit = '");
  Serial.print(rawUnit);
  Serial.println("'");
  Serial.print("  rawKey  = '");
  Serial.print(rawKey);
  Serial.println("'");

  // Snapshot + sanitize
  String ep = _wxSanitize(rawEp);
  String city = _wxSanitize(rawCity);
  String unit = _wxSanitize(rawUnit);
  String key = _wxSanitize(rawKey);

  Serial.println("[WX][DBG] After _wxSanitize:");
  Serial.print("  ep   = '");
  Serial.print(ep);
  Serial.println("'");
  Serial.print("  city = '");
  Serial.print(city);
  Serial.println("'");
  Serial.print("  unit = '");
  Serial.print(unit);
  Serial.println("'");
  Serial.print("  key  = '");
  Serial.print(key);
  Serial.println("'");

  // Validate config early and identify which fields are bad
  bool bad = false;
  if (ep.length() == 0) {
    Serial.println("[WX][CFG] Missing or empty: endpoint (ep)");
    bad = true;
  }
  if (city.length() == 0) {
    Serial.println("[WX][CFG] Missing or empty: city");
    bad = true;
  }
  if (unit.length() == 0) {
    Serial.println("[WX][CFG] Missing or empty: units");
    bad = true;
  }
  if (key.length() == 0) {
    Serial.println("[WX][CFG] Missing or empty: API key");
    bad = true;
  }

  if (bad) {
    Serial.println("[WX][CFG] INVALID: one or more required fields are empty");
    lastWeatherHttpCode = 400;  // local validation marker
    lastWeatherFetchMs = 0;
    noteNetResult(false, 0);
    Serial.println("[WX] ===== fetchWeather() END =====");
    return "";
  }

  // Build URL safely
  String cityQ = urlEncode(city);
  String url = ep + "?q=" + cityQ + "&appid=" + key + "&units=" + unit;

  // Diagnostics without leaking full key
  Serial.printf("[WX][CFG] epHash=%08lx cityHash=%08lx unitHash=%08lx key=%s\n",
                (unsigned long)_wxFnv1a32(ep),
                (unsigned long)_wxFnv1a32(city),
                (unsigned long)_wxFnv1a32(unit),
                _wxRedactKey(key).c_str());

  Serial.printf("[WX] WiFi status=%d connected=%d rssi=%d\n",
                (int)WiFi.status(), WiFi.isConnected() ? 1 : 0, WiFi.RSSI());
  Serial.print("[WX] URL: ");
  Serial.println(url);

  // Attempt loop: 1 attempt plus 1 retry
  const int maxAttempts = 2;

  for (int attempt = 1; attempt <= maxAttempts; ++attempt) {
    HTTPClient http;
    http.setReuse(false);
    http.setFollowRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS);
    http.setConnectTimeout(1200);
    http.setTimeout(2200);

    uint32_t t0 = millis();

    bool beginOk = false;
    if (url.startsWith("https://")) {
      static WiFiClientSecure secure;
      secure.setInsecure();
      secure.setHandshakeTimeout(30);
      secure.setTimeout(3);
      beginOk = http.begin(secure, url);
    } else {
      beginOk = http.begin(url);
    }

    if (!beginOk) {
      uint32_t blocked = millis() - t0;
      lastWeatherHttpCode = -1;
      lastWeatherFetchMs = blocked;
      noteNetResult(false, blocked);

      Serial.printf("[WX][HTTP] begin failed (attempt %d/%d) blockedMs=%lu\n",
                    attempt, maxAttempts, (unsigned long)blocked);

      http.end();

      if (attempt < maxAttempts) {
        delay(60 + (uint32_t)(esp_random() % 90));  // tiny jitter
        continue;
      }

      Serial.println("[WX] ===== fetchWeather() END =====");
      return "";
    }

    int code = http.GET();
    uint32_t blocked = millis() - t0;

    lastWeatherHttpCode = code;
    lastWeatherFetchMs = blocked;

    bool okCode = (code == HTTP_CODE_OK);
    noteNetResult(okCode, blocked);

    Serial.printf("[WX][HTTP] code=%d err=\"%s\" blockedMs=%lu attempt=%d/%d\n",
                  code, HTTPClient::errorToString(code).c_str(),
                  (unsigned long)blocked, attempt, maxAttempts);

    if (!okCode) {
      String body = http.getString();
      if (body.length()) {
        if (body.length() > 280) body = body.substring(0, 280) + "...";
        Serial.print("[WX][FAIL] body: ");
        Serial.println(body);
      } else {
        Serial.println("[WX][FAIL] no body");
      }

      http.end();

      if (attempt < maxAttempts) {
        delay(60 + (uint32_t)(esp_random() % 90));
        continue;
      }

      Serial.println("[WX] ===== fetchWeather() END =====");
      return "";
    }

    // Success code, now sanity check payload before returning
    int respLenHeader = http.getSize();  // can be -1 (chunked)
    String payload = http.getString();
    http.end();

    // Guard against pathological payloads
    if (payload.length() == 0 || payload.length() > 8192) {
      Serial.printf("[WX][FAIL] payload size suspicious: %u (hdr=%d)\n",
                    (unsigned)payload.length(), respLenHeader);
      if (attempt < maxAttempts) {
        delay(60 + (uint32_t)(esp_random() % 90));
        continue;
      }
      Serial.println("[WX] ===== fetchWeather() END =====");
      return "";
    }

    // JSON sanity parse
    DynamicJsonDocument test(1536);
    DeserializationError jerr = deserializeJson(test, payload);
    if (jerr) {
      Serial.printf("[WX][FAIL] JSON parse error: %s\n", jerr.c_str());
      if (attempt < maxAttempts) {
        delay(60 + (uint32_t)(esp_random() % 90));
        continue;
      }
      Serial.println("[WX] ===== fetchWeather() END =====");
      return "";
    }

    // Required keys check
    if (test["main"]["temp"].isNull() || test["weather"][0]["icon"].isNull()) {
      Serial.println("[WX][FAIL] JSON missing required fields (main.temp/weather[0].icon)");
      if (attempt < maxAttempts) {
        delay(60 + (uint32_t)(esp_random() % 90));
        continue;
      }
      Serial.println("[WX] ===== fetchWeather() END =====");
      return "";
    }

    Serial.printf("[WX][OK] payloadLen=%u hdrLen=%d\n",
                  (unsigned)payload.length(), respLenHeader);
    Serial.println("[WX] ===== fetchWeather() END =====");
    return payload;
  }

  // Should not be hit, but keep explicit
  Serial.println("[WX] ===== fetchWeather() END =====");
  return "";
}




String fetchForecast() {
  Serial.println("\n[FC] ===== fetchForecast() START =====");

  if (netBackoffActive()) {
    Serial.println("[FC] Backoff active, skipping forecast fetch");
    return "";
  }

  // Snapshot raw values first, so we can see what they are before sanitizing
  String rawEp = buildWeatherEndpoint("forecast");
  String rawCity = weatherCity;
  String rawUnit = weatherUnits;
  String rawKey = weatherApiKey;

  Serial.println("[FC][DBG] Raw config before sanitize:");
  Serial.print("  rawEp   = '");
  Serial.print(rawEp);
  Serial.println("'");
  Serial.print("  rawCity = '");
  Serial.print(rawCity);
  Serial.println("'");
  Serial.print("  rawUnit = '");
  Serial.print(rawUnit);
  Serial.println("'");
  Serial.print("  rawKey  = '");
  Serial.print(rawKey);
  Serial.println("'");

  // Snapshot + sanitize
  String ep = _wxSanitize(rawEp);
  String city = _wxSanitize(rawCity);
  String unit = _wxSanitize(rawUnit);
  String key = _wxSanitize(rawKey);

  Serial.println("[FC][DBG] After _wxSanitize:");
  Serial.print("  ep   = '");
  Serial.print(ep);
  Serial.println("'");
  Serial.print("  city = '");
  Serial.print(city);
  Serial.println("'");
  Serial.print("  unit = '");
  Serial.print(unit);
  Serial.println("'");
  Serial.print("  key  = '");
  Serial.print(key);
  Serial.println("'");

  bool bad = false;
  if (ep.length() == 0) {
    Serial.println("[FC][CFG] Missing or empty: endpoint (ep)");
    bad = true;
  }
  if (city.length() == 0) {
    Serial.println("[FC][CFG] Missing or empty: city");
    bad = true;
  }
  if (unit.length() == 0) {
    Serial.println("[FC][CFG] Missing or empty: units");
    bad = true;
  }
  if (key.length() == 0) {
    Serial.println("[FC][CFG] Missing or empty: API key");
    bad = true;
  }

  if (bad) {
    Serial.println("[FC][CFG] INVALID: one or more required fields are empty");
    lastForecastHttpCode = 400;
    lastForecastFetchMs = 0;
    noteNetResult(false, 0);
    Serial.println("[FC] ===== fetchForecast() END =====");
    return "";
  }

  String url = ep + "?q=" + urlEncode(city) + "&appid=" + key + "&units=" + unit;

  Serial.printf("[FC][CFG] epHash=%08lx cityHash=%08lx unitHash=%08lx key=%s\n",
                (unsigned long)_wxFnv1a32(ep),
                (unsigned long)_wxFnv1a32(city),
                (unsigned long)_wxFnv1a32(unit),
                _wxRedactKey(key).c_str());
  Serial.print("[FC] URL: ");
  Serial.println(url);

  const int maxAttempts = 2;
  for (int attempt = 1; attempt <= maxAttempts; ++attempt) {
    HTTPClient http;
    http.setReuse(false);
    http.setFollowRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS);
    http.setConnectTimeout(1200);
    http.setTimeout(2200);

    uint32_t t0 = millis();

    bool beginOk = false;
    if (url.startsWith("https://")) {
      static WiFiClientSecure secure;
      secure.setInsecure();
      secure.setHandshakeTimeout(30);
      secure.setTimeout(3);
      beginOk = http.begin(secure, url);
    } else {
      beginOk = http.begin(url);
    }

    if (!beginOk) {
      uint32_t blocked = millis() - t0;
      lastForecastHttpCode = -1;
      lastForecastFetchMs = blocked;
      noteNetResult(false, blocked);

      Serial.printf("[FC][HTTP] begin failed (attempt %d/%d) blockedMs=%lu\n",
                    attempt, maxAttempts, (unsigned long)blocked);

      http.end();
      if (attempt < maxAttempts) {
        delay(60 + (uint32_t)(esp_random() % 90));
        continue;
      }

      Serial.println("[FC] ===== fetchForecast() END =====");
      return "";
    }

    int code = http.GET();
    uint32_t blocked = millis() - t0;

    lastForecastHttpCode = code;
    lastForecastFetchMs = blocked;

    bool okCode = (code == HTTP_CODE_OK);
    noteNetResult(okCode, blocked);

    Serial.printf("[FC][HTTP] code=%d err=\"%s\" blockedMs=%lu attempt=%d/%d\n",
                  code, HTTPClient::errorToString(code).c_str(),
                  (unsigned long)blocked, attempt, maxAttempts);

    if (!okCode) {
      String body = http.getString();
      if (body.length()) {
        if (body.length() > 280) body = body.substring(0, 280) + "...";
        Serial.print("[FC][FAIL] body: ");
        Serial.println(body);
      } else {
        Serial.println("[FC][FAIL] no body");
      }
      http.end();

      if (attempt < maxAttempts) {
        delay(60 + (uint32_t)(esp_random() % 90));
        continue;
      }

      Serial.println("[FC] ===== fetchForecast() END =====");
      return "";
    }

    int respLenHeader = http.getSize();
    String payload = http.getString();
    http.end();

    if (payload.length() == 0 || payload.length() > 32768) {
      Serial.printf("[FC][FAIL] payload size suspicious: %u (hdr=%d)\n",
                    (unsigned)payload.length(), respLenHeader);
      if (attempt < maxAttempts) {
        delay(60 + (uint32_t)(esp_random() % 90));
        continue;
      }
      Serial.println("[FC] ===== fetchForecast() END =====");
      return "";
    }

    DynamicJsonDocument test(2048);
    DeserializationError jerr = deserializeJson(test, payload);
    if (jerr) {
      Serial.printf("[FC][FAIL] JSON parse error: %s\n", jerr.c_str());
      if (attempt < maxAttempts) {
        delay(60 + (uint32_t)(esp_random() % 90));
        continue;
      }
      Serial.println("[FC] ===== fetchForecast() END =====");
      return "";
    }

    if (!test["list"][0]["main"]["temp"].is<float>() || test["list"][0]["weather"][0]["description"].isNull()) {
      Serial.println("[FC][FAIL] JSON missing required fields");
      if (attempt < maxAttempts) {
        delay(60 + (uint32_t)(esp_random() % 90));
        continue;
      }
      Serial.println("[FC] ===== fetchForecast() END =====");
      return "";
    }

    Serial.printf("[FC][OK] payloadLen=%u hdrLen=%d\n",
                  (unsigned)payload.length(), respLenHeader);
    Serial.println("[FC] ===== fetchForecast() END =====");
    return payload;
  }

  Serial.println("[FC] ===== fetchForecast() END =====");
  return "";
}



String updateWeatherForecast() {
  String forecastJson = fetchForecast();
  if (!forecastJson.isEmpty()) {
    const size_t capacity = JSON_ARRAY_SIZE(40) + 40 * JSON_OBJECT_SIZE(8) + JSON_OBJECT_SIZE(2) + 14336 + 14336;
    DynamicJsonDocument doc(capacity);
    DeserializationError error = deserializeJson(doc, forecastJson);

    if (error) {
      Serial.print(F("deserializeJson() failed: "));
      Serial.println(error.f_str());
      return "JSON Parsing Error";
    }

    String forecast = "";
    for (int day = 0; day < 3; day++) {
      float temp_max = -9999;
      float temp_min = 9999;
      String description = "";
      String dayOfWeek = "";

      for (int i = day * 8; i < (day + 1) * 8; i++) {
        JsonObject obj = doc["list"][i];
        if (!obj.isNull()) {
          if (i == day * 8) {
            unsigned long timestamp = obj["dt"].as<unsigned long>();
            dayOfWeek = getDayOfWeek(timestamp);
            description = obj["weather"][0]["description"].as<String>();
          }
          float temp = obj["main"]["temp"].as<float>();
          if (temp > temp_max) temp_max = temp;
          if (temp < temp_min) temp_min = temp;
        }
      }

      if (!forecast.isEmpty()) forecast += " -- ";
      forecast += dayOfWeek + ": High:" + String(int(round(temp_max))) + ", Low:" + String(int(round(temp_min))) + ", " + description;
    }

    return forecast;
  }

  return "No forecast available";
}


// =====================================================
// WEATHER PARSE + STORE (unchanged)
// =====================================================
void fetchAndStoreWeatherData(const String& jsonPayload) {
  DynamicJsonDocument doc(4192);
  deserializeJson(doc, jsonPayload);

  globalTempActual = round(doc["main"]["temp"].as<float>());

  Serial.print(F("fetchAndStoreWeatherData"));
  Serial.println(globalTempActual);

  globalTempLow = round(doc["main"]["temp_min"].as<float>());
  globalTempHigh = round(doc["main"]["temp_max"].as<float>());
  globalDescription = doc["weather"][0]["description"].as<String>();
  globalWindSpeed = round(doc["wind"]["speed"].as<float>());
  globalCityName = doc["name"].as<String>();
  globalIcon = doc["weather"][0]["icon"].as<String>();

  g_tzOffsetSeconds = doc["timezone"] | 0;
  g_hasTzOffset = true;
  timeClient.setTimeOffset(g_tzOffsetSeconds);

  globalScrollingText = globalDescription + " -- Wind: " + String(globalWindSpeed) + "m/s";
  globalScrollingText += " -- " + forecastString;
}


// =====================================================
// MAIN DRAW (weather + clock + icon) (unchanged)
// =====================================================
void drawWeatherDataAndClock() {
  dma_display->clearScreen();

  uint16_t colorPastelBlue = dma_display->color565(100, 180, 220);
  uint16_t colorPastelRed = dma_display->color565(230, 100, 130);
  uint16_t colorPastelWhite = dma_display->color565(255, 255, 255);
  uint16_t colorPastelYellow = dma_display->color565(253, 253, 150);
  uint16_t bgColor = dma_display->color565(0, 0, 0);

  int xCursor = 0;
  int yCursor = 0;
  const int charSpacing = 4;
  const int lineSpacing = 6;

  initCityScroll(globalCityName);
  updateCityScrollBand(globalCityName);

  yCursor += lineSpacing;
  xCursor = 0;

  String highTempStr = String(globalTempHigh);

  if (highTempStr.length() == 1) highTempStr = "  " + highTempStr;
  else if (highTempStr.length() == 2) highTempStr = " " + highTempStr;
  else if (highTempStr.length() > 3) highTempStr = highTempStr.substring(0, 3);

  for (unsigned int i = 0; i < highTempStr.length(); i++) {
    drawCharWithCustomFont(xCursor, yCursor, highTempStr[i], colorPastelRed, bgColor);
    xCursor += charSpacing;
  }

  String spaces = "  ";

  String nowLabel = spaces + "Now";
  for (unsigned int i = 0; i < nowLabel.length(); i++) {
    drawCharWithCustomFont(xCursor, yCursor, nowLabel[i], colorPastelYellow, bgColor);
    xCursor += charSpacing;
  }

  yCursor += 6;
  xCursor = 0;

  String lowTempStr = String(globalTempLow);

  if (lowTempStr.length() == 1) lowTempStr = "  " + lowTempStr;
  else if (lowTempStr.length() == 2) lowTempStr = " " + lowTempStr;
  else if (lowTempStr.length() > 3) lowTempStr = lowTempStr.substring(0, 3);

  for (unsigned int i = 0; i < lowTempStr.length(); i++) {
    drawCharWithCustomFont(xCursor, yCursor, lowTempStr[i], colorPastelBlue, bgColor);
    xCursor += charSpacing;
  }

  String currentTempStr = String(globalTempActual);
  if (currentTempStr.length() == 1) currentTempStr = "  " + currentTempStr;
  else if (currentTempStr.length() == 2) currentTempStr = " " + currentTempStr;
  else if (currentTempStr.length() > 3) currentTempStr = currentTempStr.substring(0, 3);
  currentTempStr = spaces + currentTempStr;

  for (unsigned int i = 0; i < currentTempStr.length(); i++) {
    drawCharWithCustomFont(xCursor, yCursor, currentTempStr[i], colorPastelYellow, bgColor);
    xCursor += charSpacing;
  }

  yCursor += 6;
  xCursor = 0;
  for (unsigned int i = 0; i < strlen(globalDescription.c_str()); i++) {
    drawCharWithCustomFont(xCursor, yCursor, globalDescription[i], colorPastelWhite, bgColor);
    xCursor += charSpacing;
  }

  yCursor += 6;
  xCursor = 0;

  drawDigitalClock();

  int iconWidth = 32;
  int iconHeight = 25;
  (void)iconHeight;

  int startX = PANEL_RES_X - iconWidth;
  int startY = 0;

  if (strcmp(globalIcon.c_str(), "01d") == 0 || strcmp(globalIcon.c_str(), "01n") == 0) {
    drawIconDirectly(w01d, startX, startY);
  } else if (strcmp(globalIcon.c_str(), "02d") == 0 || strcmp(globalIcon.c_str(), "02n") == 0) {
    drawIconDirectly(w02d, startX, startY);
  } else if (strcmp(globalIcon.c_str(), "03d") == 0 || strcmp(globalIcon.c_str(), "03n") == 0) {
    drawIconDirectly(w03d, startX, startY);
  } else if (strcmp(globalIcon.c_str(), "04d") == 0 || strcmp(globalIcon.c_str(), "04n") == 0) {
    drawIconDirectly(w04d, startX, startY);
  } else if (strcmp(globalIcon.c_str(), "09d") == 0 || strcmp(globalIcon.c_str(), "09n") == 0) {
    drawIconDirectly(w09d, startX, startY);
  } else if (strcmp(globalIcon.c_str(), "10d") == 0 || strcmp(globalIcon.c_str(), "10n") == 0) {
    drawIconDirectly(w10d, startX, startY);
  } else if (strcmp(globalIcon.c_str(), "11d") == 0 || strcmp(globalIcon.c_str(), "11n") == 0) {
    drawIconDirectly(w11d, startX, startY);
  } else if (strcmp(globalIcon.c_str(), "13d") == 0 || strcmp(globalIcon.c_str(), "13n") == 0) {
    drawIconDirectly(w13d, startX, startY);
  } else if (strcmp(globalIcon.c_str(), "50d") == 0 || strcmp(globalIcon.c_str(), "50n") == 0) {
    drawIconDirectly(w50d, startX, startY);
  }
}

bool updateWeatherDisplay() {

  String weatherJson = fetchWeather();
  if (weatherJson.isEmpty()) {
    if (!screenDrawnOnce) {
      weatherReady = false;
    }
    lastFetchNote = "WX FAIL code:" + String(lastWeatherHttpCode);
    return false;
  }

  fetchAndStoreWeatherData(weatherJson);

  if (globalIcon.length() == 0) {
    weatherReady = false;
    lastFetchNote = "WX icon blank";
    return false;
  }

  weatherReady = true;

  if (!g_bootInProgress) {
    drawWeatherDataAndClock();
    screenDrawnOnce = true;
  }

  return true;
}

bool updateForecastAndStore() {
  String fs = updateWeatherForecast();

  if (fs.length() == 0 || fs == "No forecast available" || fs == "JSON Parsing Error") {
    forecastReady = false;
    lastFetchNote = "FC parse fail";
    return false;
  }

  forecastString = fs;
  forecastReady = true;
  return true;
}


// =====================================================
// SCROLLING (bottom) (unchanged)
// =====================================================
void updateScrollingText() {
  int offsetfromright = 33;
  if (millis() - lastScrollUpdate > scrollInterval) {
    scrollX -= scrollSpeed;
    lastScrollUpdate = millis();

    int textWidth = calculateTextWidth(globalScrollingText);

    if (scrollX < -textWidth) {
      scrollX = PANEL_RES_X - offsetfromright;
    }

    dma_display->fillRect(0, PANEL_RES_Y - 14, PANEL_RES_X - offsetfromright, 5, dma_display->color565(0, 0, 0));

    if (scrollX + textWidth > 0) {
      drawScrollingText(scrollX, PANEL_RES_Y - 14, globalScrollingText, dma_display->color565(255, 255, 255), dma_display->color565(0, 0, 0));
    }
  }
}

int calculateTextWidth(String text) {
  return text.length() * 4;
}

void drawScrollingText(int x, int y, String text, uint16_t color, uint16_t bgcolor) {
  int offsetfromright = 33;
  int max_x = PANEL_RES_X - offsetfromright;

  for (unsigned int i = 0; i < text.length(); i++) {
    int char_x = x + (i * 4);
    if (char_x + 3 <= max_x) {
      drawCharWithCustomFont(char_x, y, text[i], color, bgcolor);
    } else {
      break;
    }
  }
}


// =====================================================
// CITY SCROLL (top) (unchanged)
// =====================================================
void initCityScroll(const String& cityIn) {
  String city = cityIn;
  city.trim();

  int availW = PANEL_RES_X - CITY_OFFSET_RIGHT;
  int w = textWidthPx3x5(city);

  cityNeedsScroll = (w > availW);
  cityScrollX = 0;

  if (cityNeedsScroll) {
    cityPaused = true;
    cityPauseStart = millis();
  } else {
    cityPaused = false;
  }
}

void updateCityScrollBand(const String& cityIn) {
  String city = cityIn;
  city.trim();

  int availW = PANEL_RES_X - CITY_OFFSET_RIGHT;
  int w = textWidthPx3x5(city);

  cityNeedsScroll = (w > availW);

  if (millis() - lastCityScrollUpdate < cityScrollInterval) return;
  lastCityScrollUpdate = millis();

  dma_display->fillRect(0, CITY_Y, availW, CITY_H, UI_BLACK);

  if (!cityNeedsScroll) {
    int x = (availW - w) / 2;
    if (x < 0) x = 0;
    drawScrollingText(x, CITY_Y, city, UI_WHITE, UI_BLACK);
    return;
  }

  if (cityPaused) {
    drawScrollingText(0, CITY_Y, city, UI_WHITE, UI_BLACK);
    if (millis() - cityPauseStart >= cityPauseMs) cityPaused = false;
    return;
  }

  cityScrollX -= 1;

  if (cityScrollX < -w) {
    cityScrollX = availW;
    cityPaused = true;
    cityPauseStart = millis();
  }

  drawScrollingText(cityScrollX, CITY_Y, city, UI_WHITE, UI_BLACK);
}


// =====================================================
// DAY OF WEEK
// =====================================================
String getDayOfWeek(long utcTimestamp) {
  // OpenWeather sunrise/sunset etc are UTC
  time_t localEpoch = (time_t)(utcTimestamp + g_tzOffsetSeconds);
  struct tm* timeinfo = gmtime(&localEpoch);  // again, not localtime

  if (!timeinfo) return "";

  static const char* days[] = { "Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat" };
  return String(days[timeinfo->tm_wday]);
}


void applyWifiCustomParams(
  const char* city,
  const char* animTag,
  const int* brightness,
  const bool* sleepEnabled,
  const int* sleepStartHour,
  const int* sleepEndHour,
  const int* weatherUpdateMins,
  const int* checkinUpdateMins,
  const int* weatherModeSeconds,
  const int* animModeSeconds,
  const int* clockModeSeconds,
  const int* adAnimSeconds,
  const char* weatherBaseUrl,
  const char* checkinBaseUrl,
  bool applyNow) {
  // ----------------------------
  // City
  // ----------------------------
  if (city) {
    String c = String(city);
    c.trim();
    if (c.length() > 0) {
      weatherCity = c;
      custom_parameter.setValue(weatherCity.c_str(), 20);
    }
  }

  // ----------------------------
  // Animation Tag
  // ----------------------------
  if (animTag) {
    String clean = cleanTagFromString(String(animTag));
    if (clean.length() > 0) {
      g_animTag = clean;
      strncpy(animTagBuf, clean.c_str(), sizeof(animTagBuf));
      animTagBuf[sizeof(animTagBuf) - 1] = '\0';
      p_animTag.setValue(animTagBuf, 17);
      applyTagAndPaths(g_animTag);
    }
  }

  // ----------------------------
  // Brightness
  // ----------------------------
  if (brightness) {
    g_brightnessLevel = clamp15(*brightness);
    snprintf(brightnessBuf, sizeof(brightnessBuf), "%d", g_brightnessLevel);
    p_brightness.setValue(brightnessBuf, 2);

    if (applyNow) applyBrightness();
  }

  // ----------------------------
  // Sleep settings
  // ----------------------------
  if (sleepEnabled) {
    g_sleepEnabled = *sleepEnabled;
    strncpy(sleepEnabledBuf, g_sleepEnabled ? "1" : "0", sizeof(sleepEnabledBuf));
    sleepEnabledBuf[sizeof(sleepEnabledBuf) - 1] = '\0';
    p_sleepEnabled.setValue(sleepEnabledBuf, 2);
  }

  if (sleepStartHour) {
    g_sleepStartHour = clampHour(*sleepStartHour);
    snprintf(sleepStartBuf, sizeof(sleepStartBuf), "%d", g_sleepStartHour);
    p_sleepStart.setValue(sleepStartBuf, 3);
  }

  if (sleepEndHour) {
    g_sleepEndHour = clampHour(*sleepEndHour);
    snprintf(sleepEndBuf, sizeof(sleepEndBuf), "%d", g_sleepEndHour);
    p_sleepEnd.setValue(sleepEndBuf, 3);
  }

  // ----------------------------
  // Update intervals (minutes)
  // ----------------------------
  if (weatherUpdateMins) {
    g_weatherUpdateMins = clampMins(*weatherUpdateMins, 5, 1440);
    snprintf(weatherUpdateBuf, sizeof(weatherUpdateBuf), "%d", g_weatherUpdateMins);
    p_weatherUpdateMins.setValue(weatherUpdateBuf, 5);
  }

  if (checkinUpdateMins) {
    g_checkinUpdateMins = clampMins(*checkinUpdateMins, 5, 1440);
    snprintf(checkinUpdateBuf, sizeof(checkinUpdateBuf), "%d", g_checkinUpdateMins);
    p_checkinUpdateMins.setValue(checkinUpdateBuf, 5);
  }

  // ----------------------------
  // Mode durations (seconds)
  // ----------------------------
  if (weatherModeSeconds) {
    g_weatherModeSeconds = clampMins(*weatherModeSeconds, 1, 3600);
    snprintf(weatherModeSecsBuf, sizeof(weatherModeSecsBuf), "%d", g_weatherModeSeconds);
    p_weatherModeSecs.setValue(weatherModeSecsBuf, 6);
  }

  if (animModeSeconds) {
    g_animModeSeconds = clampMins(*animModeSeconds, 1, 3600);
    snprintf(animModeSecsBuf, sizeof(animModeSecsBuf), "%d", g_animModeSeconds);
    p_animModeSecs.setValue(animModeSecsBuf, 6);
  }

  if (clockModeSeconds) {
    g_clockModeSeconds = clampMins(*clockModeSeconds, 0, 3600);
    snprintf(clockModeSecsBuf, sizeof(clockModeSecsBuf), "%d", g_clockModeSeconds);
    p_clockModeSecs.setValue(clockModeSecsBuf, 6);
  }

  if (adAnimSeconds) {
    g_adAnimSeconds = clampSecs(*adAnimSeconds, 1, 3600);
    snprintf(adAnimSecBuf, sizeof(adAnimSecBuf), "%d", g_adAnimSeconds);
    p_adAnimSecs.setValue(adAnimSecBuf, 5);

    if (applyNow) {
      adAnim.showDurationMs = (uint32_t)g_adAnimSeconds * 1000UL;
    }
  }

  // ----------------------------
  // Base URLs
  // ----------------------------
  if (weatherBaseUrl) {
    g_weatherBaseUrl = stripTrailingSlashes(String(weatherBaseUrl));
    if (g_weatherBaseUrl.length() == 0) g_weatherBaseUrl = "https://api.openweathermap.org/data/2.5";

    strncpy(weatherBaseUrlBuf, g_weatherBaseUrl.c_str(), sizeof(weatherBaseUrlBuf));
    weatherBaseUrlBuf[sizeof(weatherBaseUrlBuf) - 1] = '\0';
    p_weatherBaseUrl.setValue(weatherBaseUrlBuf, sizeof(weatherBaseUrlBuf));
  }

  if (checkinBaseUrl) {
    g_checkinBaseUrl = stripTrailingSlashes(String(checkinBaseUrl));
    if (g_checkinBaseUrl.length() == 0) g_checkinBaseUrl = "https://www.auroradisplay.ca";

    strncpy(checkinBaseUrlBuf, g_checkinBaseUrl.c_str(), sizeof(checkinBaseUrlBuf));
    checkinBaseUrlBuf[sizeof(checkinBaseUrlBuf) - 1] = '\0';
    p_checkinBaseUrl.setValue(checkinBaseUrlBuf, sizeof(checkinBaseUrlBuf));
  }

  // Optional immediate UI refresh if needed later:
  // if (applyNow && g_uiMode == UI_WEATHER && weatherReady) {
  //   drawWeatherDataAndClock();
  // }
}




// =====================================================
// CONFIG SAVE/LOAD (unchanged, except uses clampMins now declared properly)
// =====================================================
void saveConfig() {
  DynamicJsonDocument doc(2048);

  // ----------------------------
  // Basics / identity
  // ----------------------------
  doc["City"] = custom_parameter.getValue();
  doc["bin_sha256"] = g_binSha256;

  // ----------------------------
  // Animation Tag (clean + apply)
  // ----------------------------
  String rawTag = String(p_animTag.getValue());
  rawTag.trim();
  String cleanTag = cleanTagFromString(rawTag);

  doc["animTag"] = cleanTag;
  g_animTag = cleanTag;
  applyTagAndPaths(cleanTag);

  doc["animVer"] = g_animVer;

  // ----------------------------
  // Sleep settings
  // ----------------------------
  g_sleepEnabled = parseBool01(p_sleepEnabled.getValue(), g_sleepEnabled);
  g_sleepStartHour = clampHour(parseIntOrDefault(p_sleepStart.getValue(), g_sleepStartHour));
  g_sleepEndHour = clampHour(parseIntOrDefault(p_sleepEnd.getValue(), g_sleepEndHour));

  doc["sleepEnabled"] = g_sleepEnabled;
  doc["sleepStart"] = g_sleepStartHour;
  doc["sleepEnd"] = g_sleepEndHour;

  // ----------------------------
  // Timers (minutes)
  // ----------------------------
  g_weatherUpdateMins = clampMins(parseIntOrDefault(p_weatherUpdateMins.getValue(), g_weatherUpdateMins), 5, 1440);
  g_checkinUpdateMins = clampMins(parseIntOrDefault(p_checkinUpdateMins.getValue(), g_checkinUpdateMins), 5, 1440);

  doc["wxMins"] = g_weatherUpdateMins;
  doc["chkMins"] = g_checkinUpdateMins;

  snprintf(weatherUpdateBuf, sizeof(weatherUpdateBuf), "%d", g_weatherUpdateMins);
  snprintf(checkinUpdateBuf, sizeof(checkinUpdateBuf), "%d", g_checkinUpdateMins);
  p_weatherUpdateMins.setValue(weatherUpdateBuf, 5);
  p_checkinUpdateMins.setValue(checkinUpdateBuf, 5);

  // ----------------------------
  // Weather/Animation/Clock mode durations (seconds) - NEW KEYS
  // Weather screen time vs Animation screen time (e.g., 30/10)
  // ----------------------------
  g_weatherModeSeconds = clampMins(parseIntOrDefault(p_weatherModeSecs.getValue(), g_weatherModeSeconds), 1, 3600);
  g_animModeSeconds = clampMins(parseIntOrDefault(p_animModeSecs.getValue(), g_animModeSeconds), 1, 3600);
  g_clockModeSeconds = clampMins(parseIntOrDefault(p_clockModeSecs.getValue(), g_clockModeSeconds), 0, 3600);  // allow 0 if desired

  doc["wModeSecs"] = g_weatherModeSeconds;
  doc["aModeSecs"] = g_animModeSeconds;
  doc["cModeSecs"] = g_clockModeSeconds;

  snprintf(weatherModeSecsBuf, sizeof(weatherModeSecsBuf), "%d", g_weatherModeSeconds);
  snprintf(animModeSecsBuf, sizeof(animModeSecsBuf), "%d", g_animModeSeconds);
  snprintf(clockModeSecsBuf, sizeof(clockModeSecsBuf), "%d", g_clockModeSeconds);

  p_weatherModeSecs.setValue(weatherModeSecsBuf, 6);
  p_animModeSecs.setValue(animModeSecsBuf, 6);
  p_clockModeSecs.setValue(clockModeSecsBuf, 6);

  // ----------------------------
  // Ad animation duration (seconds) - legacy key kept
  // ----------------------------
  g_adAnimSeconds = clampSecs(parseIntOrDefault(p_adAnimSecs.getValue(), g_adAnimSeconds), 1, 3600);
  doc["adSecs"] = g_adAnimSeconds;

  snprintf(adAnimSecBuf, sizeof(adAnimSecBuf), "%d", g_adAnimSeconds);
  p_adAnimSecs.setValue(adAnimSecBuf, 5);

  // apply immediately
  adAnim.showDurationMs = (uint32_t)g_adAnimSeconds * 1000UL;

  // ----------------------------
  // Brightness
  // ----------------------------
  g_brightnessLevel = clamp15(parseIntOrDefault(p_brightness.getValue(), g_brightnessLevel));
  doc["brightness"] = g_brightnessLevel;

  snprintf(brightnessBuf, sizeof(brightnessBuf), "%d", g_brightnessLevel);
  p_brightness.setValue(brightnessBuf, 2);
  applyBrightness();

  // ----------------------------
  // Ensure runtime city is in sync
  // ----------------------------
  weatherCity = String(custom_parameter.getValue());


  // ----------------------------
  // Base URLs (Weather + Check-in)
  // ----------------------------
  g_weatherBaseUrl = stripTrailingSlashes(String(p_weatherBaseUrl.getValue()));
  g_checkinBaseUrl = stripTrailingSlashes(String(p_checkinBaseUrl.getValue()));

  if (g_weatherBaseUrl.length() == 0) g_weatherBaseUrl = "https://api.openweathermap.org/data/2.5";
  if (g_checkinBaseUrl.length() == 0) g_checkinBaseUrl = "https://www.auroradisplay.ca";

  doc["wxBase"] = g_weatherBaseUrl;
  doc["chkBase"] = g_checkinBaseUrl;

  strncpy(weatherBaseUrlBuf, g_weatherBaseUrl.c_str(), sizeof(weatherBaseUrlBuf));
  weatherBaseUrlBuf[sizeof(weatherBaseUrlBuf) - 1] = '\0';
  p_weatherBaseUrl.setValue(weatherBaseUrlBuf, sizeof(weatherBaseUrlBuf));

  strncpy(checkinBaseUrlBuf, g_checkinBaseUrl.c_str(), sizeof(checkinBaseUrlBuf));
  checkinBaseUrlBuf[sizeof(checkinBaseUrlBuf) - 1] = '\0';
  p_checkinBaseUrl.setValue(checkinBaseUrlBuf, sizeof(checkinBaseUrlBuf));



  // ----------------------------
  // Write file
  // ----------------------------
  File configFile = LittleFS.open("/config.json", "w");
  if (!configFile) {
    Serial.println("Failed to open config file for writing");
    return;
  }

  serializeJson(doc, Serial);
  serializeJson(doc, configFile);
  configFile.close();
}


void saveConfigCallback() {
  Serial.println("Should save config");
  saveConfig();
}

bool loadConfig() {
  File configFile = LittleFS.open("/config.json", "r");
  if (!configFile) {
    Serial.println("Failed to open config file for reading");
    return false;
  }

  DynamicJsonDocument doc(2048);
  DeserializationError err = deserializeJson(doc, configFile);
  configFile.close();

  if (err) {
    Serial.println("Failed to parse config file");
    return false;
  }

  // ----------------------------
  // City (legacy key: "City")
  // ----------------------------
  const char* cityValue = doc["City"] | "";
  if (cityValue && *cityValue) {
    custom_parameter.setValue(cityValue, 20);
  }

  // ----------------------------
  // Animation Tag
  // ----------------------------
  const char* tagValue = doc["animTag"] | "";
  if (tagValue && *tagValue) {
    strncpy(animTagBuf, tagValue, sizeof(animTagBuf));
    animTagBuf[sizeof(animTagBuf) - 1] = '\0';
  } else {
    animTagBuf[0] = '\0';
  }
  p_animTag.setValue(animTagBuf, 17);

  g_animTag = String(animTagBuf);
  applyTagAndPaths(g_animTag);

  // ----------------------------
  // Weather/Anim cycle durations (NEW keys)
  // wModeSecs: weather screen seconds
  // aModeSecs: animation seconds
  // cModeSecs: optional "clock mode" seconds (if used elsewhere)
  // Legacy fallback keys:
  // clkSecs -> cModeSecs
  // aniSecs -> aModeSecs
  // ----------------------------
  int wSecs = doc["wModeSecs"] | g_weatherModeSeconds;
  int aSecs = doc["aModeSecs"] | (doc["aniSecs"] | g_animModeSeconds);
  int cSecs = doc["cModeSecs"] | (doc["clkSecs"] | g_clockModeSeconds);

  g_weatherModeSeconds = clampMins(wSecs, 1, 3600);
  g_animModeSeconds = clampMins(aSecs, 1, 3600);
  g_clockModeSeconds = clampMins(cSecs, 0, 3600);  // allow 0 if you want "off"

  snprintf(weatherModeSecsBuf, sizeof(weatherModeSecsBuf), "%d", g_weatherModeSeconds);
  snprintf(animModeSecsBuf, sizeof(animModeSecsBuf), "%d", g_animModeSeconds);
  snprintf(clockModeSecsBuf, sizeof(clockModeSecsBuf), "%d", g_clockModeSeconds);

  p_weatherModeSecs.setValue(weatherModeSecsBuf, 6);
  p_animModeSecs.setValue(animModeSecsBuf, 6);
  p_clockModeSecs.setValue(clockModeSecsBuf, 6);

  // ----------------------------
  // Binary metadata
  // ----------------------------
  g_binSha256 = String((const char*)(doc["bin_sha256"] | ""));
  g_animVer = doc["animVer"] | 0;

  // ----------------------------
  // Sleep settings
  // ----------------------------
  g_sleepEnabled = doc["sleepEnabled"] | g_sleepEnabled;
  g_sleepStartHour = clampHour(doc["sleepStart"] | g_sleepStartHour);
  g_sleepEndHour = clampHour(doc["sleepEnd"] | g_sleepEndHour);

  strncpy(sleepEnabledBuf, g_sleepEnabled ? "1" : "0", sizeof(sleepEnabledBuf));
  sleepEnabledBuf[sizeof(sleepEnabledBuf) - 1] = '\0';

  snprintf(sleepStartBuf, sizeof(sleepStartBuf), "%d", g_sleepStartHour);
  snprintf(sleepEndBuf, sizeof(sleepEndBuf), "%d", g_sleepEndHour);

  p_sleepEnabled.setValue(sleepEnabledBuf, 2);
  p_sleepStart.setValue(sleepStartBuf, 3);
  p_sleepEnd.setValue(sleepEndBuf, 3);

  // ----------------------------
  // Update timers (minutes)
  // ----------------------------
  g_weatherUpdateMins = clampMins(doc["wxMins"] | g_weatherUpdateMins, 5, 1440);
  g_checkinUpdateMins = clampMins(doc["chkMins"] | g_checkinUpdateMins, 5, 1440);

  snprintf(weatherUpdateBuf, sizeof(weatherUpdateBuf), "%d", g_weatherUpdateMins);
  snprintf(checkinUpdateBuf, sizeof(checkinUpdateBuf), "%d", g_checkinUpdateMins);

  p_weatherUpdateMins.setValue(weatherUpdateBuf, 5);
  p_checkinUpdateMins.setValue(checkinUpdateBuf, 5);

  // ----------------------------
  // Brightness
  // ----------------------------
  g_brightnessLevel = clamp15(doc["brightness"] | g_brightnessLevel);
  snprintf(brightnessBuf, sizeof(brightnessBuf), "%d", g_brightnessLevel);
  p_brightness.setValue(brightnessBuf, 2);


  // ----------------------------
  // Base URLs (Weather + Check-in)
  // ----------------------------
  const char* wxBase = doc["wxBase"] | "https://api.openweathermap.org/data/2.5";
  const char* chkBase = doc["chkBase"] | "https://www.auroradisplay.ca";

  g_weatherBaseUrl = stripTrailingSlashes(String(wxBase));
  g_checkinBaseUrl = stripTrailingSlashes(String(chkBase));

  if (g_weatherBaseUrl.length() == 0) g_weatherBaseUrl = "https://api.openweathermap.org/data/2.5";
  if (g_checkinBaseUrl.length() == 0) g_checkinBaseUrl = "https://www.auroradisplay.ca";

  strncpy(weatherBaseUrlBuf, g_weatherBaseUrl.c_str(), sizeof(weatherBaseUrlBuf));
  weatherBaseUrlBuf[sizeof(weatherBaseUrlBuf) - 1] = '\0';
  p_weatherBaseUrl.setValue(weatherBaseUrlBuf, sizeof(weatherBaseUrlBuf));

  strncpy(checkinBaseUrlBuf, g_checkinBaseUrl.c_str(), sizeof(checkinBaseUrlBuf));
  checkinBaseUrlBuf[sizeof(checkinBaseUrlBuf) - 1] = '\0';
  p_checkinBaseUrl.setValue(checkinBaseUrlBuf, sizeof(checkinBaseUrlBuf));



  // ----------------------------
  // Ensure weatherCity is set from the portal value (or restore default)
  // ----------------------------
  String cv = String(custom_parameter.getValue());
  cv.trim();
  if (cv.length() > 0) {
    weatherCity = cv;
  } else {
    custom_parameter.setValue(weatherCity.c_str(), 20);
  }

  // ----------------------------
  // Ad animation duration (separate feature, keep legacy key: "adSecs")
  // ----------------------------
  g_adAnimSeconds = clampSecs((int)(doc["adSecs"] | g_adAnimSeconds), 1, 3600);

  snprintf(adAnimSecBuf, sizeof(adAnimSecBuf), "%d", g_adAnimSeconds);
  p_adAnimSecs.setValue(adAnimSecBuf, 5);

  adAnim.showDurationMs = (uint32_t)g_adAnimSeconds * 1000UL;

  return true;
}

// =====================================================
// DOWNLOAD / ATOMIC SWAP (BIN updates) (unchanged)
// =====================================================
static bool downloadToTempFile(
  const String& url,
  const String& finalPath,
  size_t expectedSize,
  uint32_t timeoutMs,
  bool secureOverride,
  const String& uiCode) {

  const String tmpPath = finalPath + ".tmp";

  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("[DL] WiFi not connected");
    return false;
  }

  if (LittleFS.exists(tmpPath)) {
    Serial.printf("[DL] Removing stale tmp: %s\n", tmpPath.c_str());
    LittleFS.remove(tmpPath);
  }

  HTTPClient http;
  http.setFollowRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS);
  http.setTimeout(timeoutMs);

  static WiFiClient plain;
  static WiFiClientSecure secure;

  bool urlIsHttps = url.startsWith("https://");
  bool useSecure = secureOverride || urlIsHttps;

  if (useSecure) {
    secure.setInsecure();
    secure.setHandshakeTimeout(30);
    secure.setTimeout(timeoutMs / 1000);
  } else {
    plain.setTimeout(timeoutMs / 1000);
  }

  Serial.printf("[DL] BEGIN %s (useSecure=%s)\n", url.c_str(), useSecure ? "true" : "false");

  bool okBegin = useSecure ? http.begin(secure, url) : http.begin(plain, url);

  if (!okBegin) {
    Serial.println("[DL] http.begin failed");
    http.end();
    return false;
  }

  Serial.printf("[DL] GET %s\n", url.c_str());
  int code = http.GET();
  if (code <= 0) {
    Serial.printf("[DL] HTTP GET failed: %d (%s)\n",
                  code, http.errorToString(code).c_str());
    http.end();
    return false;
  }

  if (code != HTTP_CODE_OK) {
    Serial.printf("[DL] HTTP GET failed: %d\n", code);
    http.end();
    return false;
  }

  int len = http.getSize();
  Serial.printf("[DL] Content-Length: %d\n", len);
  const int contentLen = len;
  size_t totalLen = 0;

  if (expectedSize > 0) totalLen = expectedSize;
  else if (contentLen > 0) totalLen = (size_t)contentLen;

  if (uiCode.length()) {
    int pct0 = (totalLen > 0) ? 0 : -1;
    drawBinDownloadProgress3x5(uiCode, pct0, 0, totalLen);
  }

  if (expectedSize > 0 && len > 0 && (size_t)len != expectedSize) {
    Serial.printf("[DL] Size mismatch header=%d expected=%u\n", len, (unsigned)expectedSize);
    http.end();
    return false;
  }

  File f = LittleFS.open(tmpPath, FILE_WRITE);
  if (!f) {
    Serial.printf("[DL] Failed to open tmp for write: %s\n", tmpPath.c_str());
    http.end();
    return false;
  }

  WiFiClient* stream = http.getStreamPtr();

  // Heap buffer (avoids large stack usage)
  static const size_t kBufSize = 2048;
  std::unique_ptr<uint8_t[]> buf(new (std::nothrow) uint8_t[kBufSize]);
  if (!buf) {
    Serial.println("[DL] Buffer allocation failed");
    f.close();
    http.end();
    LittleFS.remove(tmpPath);
    return false;
  }

  size_t total = 0;
  uint32_t lastDataMs = millis();
  uint32_t lastProgMs = 0;
  uint32_t lastUiMs = 0;

  while (http.connected() && (len > 0 || len == -1)) {
    size_t avail = stream->available();
    if (avail) {
      size_t toRead = (avail > kBufSize) ? kBufSize : avail;

      // readBytes expects char*
      int r = stream->readBytes(reinterpret_cast<char*>(buf.get()), toRead);
      if (r <= 0) {
        yield();
        continue;
      }

      size_t w = f.write(buf.get(), (size_t)r);
      if (w != (size_t)r) {
        Serial.printf("[DL] Write failed (wrote %u of %d)\n", (unsigned)w, r);
        f.close();
        http.end();
        LittleFS.remove(tmpPath);
        return false;
      }

      total += w;
      lastDataMs = millis();

      if (len > 0) len -= r;

      uint32_t nowMs = millis();
      if (uiCode.length() && (nowMs - lastUiMs) > 250) {
        lastUiMs = nowMs;

        int pct = -1;
        if (totalLen > 0) {
          pct = (int)((total * 100UL) / totalLen);
          if (pct > 100) pct = 100;
        }
        drawBinDownloadProgress3x5(uiCode, pct, total, totalLen);
      }

      if (millis() - lastProgMs > 1000) {
        lastProgMs = millis();
        Serial.printf("[DL] %u bytes\n", (unsigned)total);
      }
    } else {
      if (uiCode.length()) {
        uint32_t nowMs = millis();
        if ((nowMs - lastUiMs) > 250) {
          lastUiMs = nowMs;

          int pct = -1;
          if (totalLen > 0) {
            pct = (int)((total * 100UL) / totalLen);
            if (pct > 100) pct = 100;
          }
          drawBinDownloadProgress3x5(uiCode, pct, total, totalLen);
        }
      }

      if (millis() - lastDataMs > timeoutMs) {
        Serial.println("[DL] Stream timeout (no data)");
        f.close();
        http.end();
        LittleFS.remove(tmpPath);
        return false;
      }

      delay(2);
      yield();
    }
  }

  f.flush();
  f.close();
  http.end();

  Serial.printf("[DL] Wrote %u bytes to %s\n", (unsigned)total, tmpPath.c_str());

  if (expectedSize > 0 && total != expectedSize) {
    Serial.printf("[DL] Final size mismatch wrote=%u expected=%u\n",
                  (unsigned)total, (unsigned)expectedSize);
    LittleFS.remove(tmpPath);
    return false;
  }
  if (expectedSize == 0 && total == 0) {
    Serial.println("[DL] Downloaded 0 bytes (invalid)");
    LittleFS.remove(tmpPath);
    return false;
  }

  return true;
}


static void cleanupStaleTemp(const String& finalPath) {
  const String tmpPath = finalPath + ".tmp";
  if (LittleFS.exists(tmpPath) && LittleFS.exists(finalPath)) {
    Serial.printf("[DL] Removing stale tmp (final exists): %s\n", tmpPath.c_str());
    LittleFS.remove(tmpPath);
  }
}

static bool commitTempFile(const String& finalPath) {
  const String tmpPath = finalPath + ".tmp";
  const String bakPath = finalPath + ".bak";

  if (!LittleFS.exists(tmpPath)) {
    Serial.printf("[COMMIT] No tmp to commit: %s\n", tmpPath.c_str());
    return false;
  }

  if (LittleFS.exists(bakPath)) {
    Serial.printf("[COMMIT] Removing old bak: %s\n", bakPath.c_str());
    LittleFS.remove(bakPath);
  }

  if (LittleFS.exists(finalPath)) {
    Serial.printf("[COMMIT] Backing up %s -> %s\n", finalPath.c_str(), bakPath.c_str());
    if (!LittleFS.rename(finalPath, bakPath)) {
      Serial.println("[COMMIT] Failed to rename final -> bak");
      return false;
    }
  }

  Serial.printf("[COMMIT] Promoting %s -> %s\n", tmpPath.c_str(), finalPath.c_str());
  if (!LittleFS.rename(tmpPath, finalPath)) {
    Serial.println("[COMMIT] Failed to rename tmp -> final, attempting rollback...");

    if (LittleFS.exists(bakPath)) {
      LittleFS.rename(bakPath, finalPath);
    }
    if (LittleFS.exists(tmpPath)) {
      LittleFS.remove(tmpPath);
    }
    return false;
  }

  File f = LittleFS.open(finalPath, FILE_READ);
  if (!f) {
    Serial.println("[COMMIT] New final file can't be opened; rollback...");
    LittleFS.remove(finalPath);
    if (LittleFS.exists(bakPath)) {
      LittleFS.rename(bakPath, finalPath);
    }
    return false;
  }
  f.close();

  if (LittleFS.exists(bakPath)) {
    Serial.printf("[COMMIT] Deleting bak: %s\n", bakPath.c_str());
    LittleFS.remove(bakPath);
  }

  Serial.println("[COMMIT] Commit successful");
  return true;
}

static void recoverTempAndBackup(const String& finalPath) {
  const String tmpPath = finalPath + ".tmp";
  const String bakPath = finalPath + ".bak";

  bool hasFinal = LittleFS.exists(finalPath);
  bool hasTmp = LittleFS.exists(tmpPath);
  bool hasBak = LittleFS.exists(bakPath);

  if (hasFinal && hasTmp) {
    Serial.printf("[RECOVER] Final exists; removing stale tmp: %s\n", tmpPath.c_str());
    LittleFS.remove(tmpPath);
    return;
  }

  if (!hasFinal && hasTmp) {
    Serial.printf("[RECOVER] No final; promoting tmp: %s -> %s\n", tmpPath.c_str(), finalPath.c_str());
    LittleFS.rename(tmpPath, finalPath);
    return;
  }

  if (!hasFinal && hasBak) {
    Serial.printf("[RECOVER] No final; restoring bak: %s -> %s\n", bakPath.c_str(), finalPath.c_str());
    LittleFS.rename(bakPath, finalPath);
    return;
  }
}


// =====================================================
// FS ANIMATION (LittleFS BIN frame reader / player)
// =====================================================
int getFrameCountFromFS(const String& path) {
  File f = LittleFS.open(path, "r");
  if (!f) return 0;
  const size_t frameBytes = 64 * 32 * 2;
  size_t sz = f.size();
  f.close();
  return (int)(sz / frameBytes);
}


void startAnim(FSAnimPlayer& p) {
  // If we already know it's missing, don't keep hammering FS
  if (g_animMissing) {
    showNoAnimMessage();
    return;
  }

  // Close any previous file handle
  if (p.fileOpen) {
    p.file.close();
    p.fileOpen = false;
  }

  p.file = LittleFS.open(p.path, "r");
  if (!p.file) {
    p.playing = false;
    g_animMissing = true;
    showNoAnimMessage();
    return;
  }

  p.fileOpen = true;

  const size_t frameBytes = 64 * 32 * 2;
  size_t sz = p.file.size();
  p.frameCount = (int)(sz / frameBytes);

  if (p.frameCount <= 0) {
    p.playing = false;
    g_animMissing = true;

    if (p.fileOpen) {
      p.file.close();
      p.fileOpen = false;
    }

    uint32_t now = millis();
    if ((int32_t)(now - g_animMissingLogMs) >= 10000) {
      g_animMissingLogMs = now;
      Serial.printf("FSAnim missing: path=%s tag=%s\n", p.path.c_str(), g_animTag.c_str());
    }

    showNoAnimMessage();
    return;
  }

  // frameCount is valid here -> load timeline durations
  bool tlOk = loadTimelineDurationsFromJson(g_tagJsonPath, p.frameCount);
  if (!tlOk) {
    Serial.printf("[TL] Fallback timing in use for %s\n", g_tagJsonPath.c_str());
  }

  p.file.seek(0, SeekSet);

  // If we got frames again, clear the latch
  g_animMissing = false;

  p.playing = true;
  p.startMs = millis();
  p.frameIndex = 0;
  p.lastFrameMs = 0;
  dma_display->clearScreen();
}



void stopAnim(FSAnimPlayer& p) {

  p.playing = false;

  if (p.fileOpen) {
    p.file.close();
    p.fileOpen = false;
  }


  dma_display->clearScreen();

  if (g_uiMode == UI_WEATHER) {
    drawWeatherDataAndClock();
    // NEW: restart the "weather phase" timer whenever we return to weather
    g_weatherPhaseStartMs = millis();

  } else if (g_uiMode == UI_CLOCK) {
    drawDigitalClock();
  } else {
    showStatusScreen("ANIM", "STOPPED", "RESTARTING");
  }
}


void updateAnim(FSAnimPlayer& p) {
  // NEW: never draw frames while an overlay or pairing countdown is active,
  // or while we're in "register device" mode. The overlay owns the screen.
  if (g_btnOverlayActive || g_pairCountdownActive || g_uiMode == UI_REGDEV) {
    return;
  }

  if (!p.playing) return;

  if (millis() - p.startMs >= p.showDurationMs) {
    if (g_uiMode == UI_ANIM) {
      p.startMs = millis();
      p.frameIndex = 0;
      p.lastFrameMs = 0;
      return;
    }
    stopAnim(p);
    return;
  }

  uint16_t frameDelay = p.frameDelayMs;  // fallback
  if (g_timelineLoaded && p.frameIndex >= 0 && p.frameIndex < g_timelineCount) {
    frameDelay = g_timelineDurMs[p.frameIndex];
  }

  if (millis() - p.lastFrameMs < frameDelay) return;

  p.lastFrameMs = millis();

  if (p.frameCount <= 0) return;

  if (!readNextFrameFromOpenFile(p, frameBuf)) {
    if (g_uiMode == UI_ANIM) {
      p.playing = false;
      showStatusScreen("ANIM", "READ FAIL", String(p.path));
      return;
    }
    stopAnim(p);
    return;
  }

  drawFrame64x32_RAM(frameBuf, 0, 0);

  p.frameIndex++;
  if (p.frameIndex >= p.frameCount) p.frameIndex = 0;
}





void drawFrame64x32_RAM(const uint16_t* frame, int xPos, int yPos) {
  // Fast path: draw whole 64x32 bitmap in one call
  dma_display->drawRGBBitmap(xPos, yPos, frame, 64, 32);
}





// =====================================================
// BUTTON: WiFiManager reset helper (10s window)
// =====================================================
void checkButton(WiFiManager& wm) {

#if !ENABLE_BUTTON_INPUT
  (void)wm;
  return;
#endif
  // existing code...
  const uint32_t windowMs = 10000;
  uint32_t startMs = millis();

  bool longPressTriggered = false;

  while (millis() - startMs < windowMs) {
    uint32_t now = millis();
    bool reading = buttonPressedNow();

    if (reading != g_btnLastReading) {
      g_btnLastReading = reading;
      g_btnChangeMs = now;
    }

    if (now - g_btnChangeMs > BTN_DEBOUNCE_MS) {
      if (reading != g_btnStablePressed) {
        g_btnStablePressed = reading;

        if (g_btnStablePressed) {
          g_btnPressStartMs = now;
          g_btnLongHandled = false;
          Serial.println("Button detected");
        } else {
          if (!g_btnLongHandled && (now - g_btnPressStartMs) < BTN_LONGPRESS_MS) {
            Serial.println("Short Button Pressed");
          }
        }
      }
    }

    if (g_btnStablePressed && !g_btnLongHandled && (now - g_btnPressStartMs >= BTN_LONGPRESS_MS)) {
      g_btnLongHandled = true;
      longPressTriggered = true;

      Serial.println("Button Held");
      Serial.println("Erasing Config, restarting");
      dma_display->clearScreen();
      showStatusScreen("RESET", "WIFI", "COMPLETE");

      wm.resetSettings();
      delay(5000);
      break;
    }

    delay(2);
    yield();
  }

  if (longPressTriggered) {
    // optional restart if desired
  }
}




// =====================================================
// BUTTON: 1-second overlay (always active)
// =====================================================
void showButton1sMessage() {
  showStatusScreen("BUTTON", "PRESSED", "1 SECOND");
}



void serviceButtonAnytime(uint32_t now) {
#if !ENABLE_BUTTON_INPUT
  // Button handling is disabled at compile time
  (void)now;
  return;
#endif

  // Simple debounced edge detection:
  // - `reading` is the raw hardware state
  // - we treat "pressed" as the transition from not-pressed -> pressed

  static bool lastReading = false;    // last raw reading
  static bool stablePressed = false;  // debounced state
  static uint32_t changeMs = 0;       // when raw reading last changed

  bool reading = buttonPressedNow();

  // If the raw reading changes, start a debounce window
  if (reading != lastReading) {
    lastReading = reading;
    changeMs = now;
  }

  // After BTN_DEBOUNCE_MS of stable input, accept it
  if ((now - changeMs) > BTN_DEBOUNCE_MS) {
    // Debounced state changed -> either just pressed or just released
    if (reading != stablePressed) {
      stablePressed = reading;

      // Only care about the "just pressed" edge
      if (stablePressed) {
        showStatusScreen(
          "BUTTON",
          "PRESSED",
          "",
          "");

        g_btnMsgUntilMs = now + BTN_MSG_SHOW_MS;
        g_btnOverlayActive = true;
        g_btnNeedsFullRedraw = true;
      }
    }
  }
}





// =====================================================
// DEMO MODE (unchanged)
// =====================================================
void demoSetCityAndFetch(const char* city) {
  if (!city || !*city) return;

  if (g_userCityBackup.length() == 0) {
    g_userCityBackup = weatherCity;
  }

  weatherCity = String(city);
  weatherCity.trim();

  showStatusScreen("DEMO", "CITY", weatherCity);

  uint32_t now = millis();
  if (!forecastReady || now >= g_demoNextForecastMs) {
    updateForecastAndStore();
    g_demoNextForecastMs = now + DEMO_FORECAST_EVERY_MS;
  }

  updateWeatherDisplay();
  initCityScroll(globalCityName);
}

void handleDemoMode() {
  if (!g_demoMode) return;
  if (WiFi.status() != WL_CONNECTED) return;

  uint32_t now = millis();

  if ((int32_t)(now - g_demoHoldUntilMs) < 0) {
    return;
  }

  if (g_demoNextSwitchMs == 0) {
    g_demoNextSwitchMs = now;
  }

  if ((int32_t)(now - g_demoNextSwitchMs) >= 0) {
    const char* city = CITY_CYCLE[g_demoCityIndex % CITY_CYCLE_COUNT];
    g_demoCityIndex = (g_demoCityIndex + 1) % CITY_CYCLE_COUNT;

    demoSetCityAndFetch(city);
    g_demoHoldUntilMs = now + DEMO_HOLD_MS;

    g_demoNextSwitchMs = now + DEMO_SWITCH_MS;
  }
}


// =====================================================
// HWID SPLASH (unchanged)
// =====================================================
String getHardwareIdString() {
  uint64_t mac = ESP.getEfuseMac();
  uint32_t hi = (uint32_t)(mac >> 32);
  uint32_t lo = (uint32_t)(mac & 0xFFFFFFFF);

  char hardware_id[13];
  snprintf(hardware_id, sizeof(hardware_id), "%04X%08X", (hi & 0xFFFF), lo);

  return String(hardware_id);  // 12 hex chars
}

void showHardwareIdSplash(uint32_t ms) {
  if (!dma_display) return;

  String hwid = getHardwareIdString();

  dma_display->clearScreen();

  drawCentered3x5(0, "DEVICE", UI_WHITE, UI_BLACK);
  drawCentered3x5(9, "HWID", UI_YELLOW, UI_BLACK);
  drawCentered3x5(18, hwid, UI_WHITE, UI_BLACK);

  delay(ms);
}


// =====================================================
// Backend sync (unchanged)
// =====================================================
bool syncSettingsFromBackendAndOverwriteWiFi(const String& url) {
  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("[CFG] WiFi not connected; cannot sync settings");
    return false;
  }

  showStatusScreen("SYNC", "FETCHING", "SETTINGS");

  HTTPClient http;
  http.setTimeout(1200);
  http.setConnectTimeout(700);
  http.setReuse(false);
  http.setFollowRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS);

  //if (!http.begin(url)) {
  bool beginOk = false;

  if (url.startsWith("https://")) {
    static WiFiClientSecure secure;
    secure.setInsecure();
    secure.setHandshakeTimeout(30);
    secure.setTimeout(3);
    beginOk = http.begin(secure, url);
  } else {
    static WiFiClient plain;
    plain.setTimeout(3);
    beginOk = http.begin(plain, url);
  }


  if (!beginOk) {
    // handle fail
  }


  if (!beginOk) {

    Serial.println("[CFG] http.begin failed");
    showStatusScreen("SYNC", "HTTP", "BEGIN FAIL");
    http.end();
    return false;
  }

  uint32_t t0 = millis();
  int code = http.GET();
  uint32_t dt = millis() - t0;

  if (code != HTTP_CODE_OK) {
    Serial.printf("[CFG] GET failed code=%d time=%ums\n", code, (unsigned)dt);
    showStatusScreen("SYNC", "HTTP FAIL", "CODE:" + String(code));
    http.end();
    return false;
  }

  String payload = http.getString();
  http.end();

  if (payload.length() < 10) {
    Serial.println("[CFG] Payload too small");
    showStatusScreen("SYNC", "BAD", "PAYLOAD");
    return false;
  }

  DynamicJsonDocument doc(2048);
  DeserializationError err = deserializeJson(doc, payload);
  if (err) {
    Serial.print("[CFG] JSON parse error: ");
    Serial.println(err.f_str());
    showStatusScreen("SYNC", "JSON", "PARSE FAIL");
    return false;
  }

  const char* newSsid = doc["wifi"]["ssid"] | "";
  const char* newPass = doc["wifi"]["pass"] | "";

  if (!newSsid || !*newSsid) {
    Serial.println("[CFG] Missing wifi.ssid");
    showStatusScreen("SYNC", "MISSING", "WIFI SSID");
    return false;
  }

  const char* newCity = doc["city"] | nullptr;
  if (newCity && *newCity) {
    custom_parameter.setValue(newCity, 20);
    weatherCity = String(newCity);
  }

  if (doc.containsKey("brightness")) {
    int b = clamp15(doc["brightness"] | g_brightnessLevel);
    g_brightnessLevel = b;
    snprintf(brightnessBuf, sizeof(brightnessBuf), "%d", b);
    p_brightness.setValue(brightnessBuf, 2);
    applyBrightness();
  }

  if (doc.containsKey("sleepEnabled")) {
    g_sleepEnabled = (doc["sleepEnabled"] | (g_sleepEnabled ? 1 : 0)) == 1;
    strncpy(sleepEnabledBuf, g_sleepEnabled ? "1" : "0", sizeof(sleepEnabledBuf));
    sleepEnabledBuf[sizeof(sleepEnabledBuf) - 1] = '\0';
    p_sleepEnabled.setValue(sleepEnabledBuf, 2);
  }
  if (doc.containsKey("sleepStart")) {
    g_sleepStartHour = clampHour(doc["sleepStart"] | g_sleepStartHour);
    snprintf(sleepStartBuf, sizeof(sleepStartBuf), "%d", g_sleepStartHour);
    p_sleepStart.setValue(sleepStartBuf, 3);
  }
  if (doc.containsKey("sleepEnd")) {
    g_sleepEndHour = clampHour(doc["sleepEnd"] | g_sleepEndHour);
    snprintf(sleepEndBuf, sizeof(sleepEndBuf), "%d", g_sleepEndHour);
    p_sleepEnd.setValue(sleepEndBuf, 3);
  }

  const char* newTag = doc["animTag"] | nullptr;
  if (newTag && *newTag) {
    strncpy(animTagBuf, newTag, sizeof(animTagBuf));
    animTagBuf[sizeof(animTagBuf) - 1] = '\0';
    p_animTag.setValue(animTagBuf, 17);

    g_animTag = String(animTagBuf);
    applyTagAndPaths(g_animTag);
  }

  saveConfig();

  showStatusScreen("SYNC", "APPLYING", "WIFI...");

  {
    WiFiManager wm;
    wm.setDebugOutput(true);
    wm.resetSettings();
  }

  WiFi.disconnect(true, true);
  delay(200);

  WiFi.mode(WIFI_STA);
  WiFi.begin(newSsid, newPass);

  uint32_t startMs = millis();
  while (WiFi.status() != WL_CONNECTED && (millis() - startMs) < 15000) {
    delay(250);
    yield();
  }

  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("[CFG] New WiFi credentials failed to connect");
    showStatusScreen("SYNC", "WIFI FAIL", "KEEP OLD?");
    return false;
  }

  Serial.printf("[CFG] Connected with new WiFi. IP=%s\n", WiFi.localIP().toString().c_str());
  showStatusScreen("SYNC", "WIFI OK", "RESTARTING");

  delay(1200);
  ESP.restart();
  return true;
}


// =====================================================
// CHECK-IN + UPDATE (QUIET MODE ADDED)
// =====================================================
//
// quiet=false: show screens + keep your 1s debug delays
// quiet=true : no screens + all those 1s delays removed (fast)
//
// NOTE: download progress still displays because that's useful.
//

bool checkInAndUpdateFromServer(const String& checkinUrl, bool quiet) {
  const uint32_t fnStartMs = millis();

  auto fail = [&](const char* why, int httpCode, uint32_t rttMs, const String& detail = "") -> bool {
    g_lastCheckinOk = false;
    g_lastCheckinHadPairing = false;
    g_lastPairCode = "";
    g_lastPairSuccess = false;    // <-- add this (you must define the global)
    g_lastPairFriendlyName = "";  //new friendly email reset
    g_lastPairOwnerEmail = "";


    g_lastCheckinHttpCode = httpCode;
    g_lastCheckinRttMs = rttMs;
    g_lastNetBlockMs = rttMs;
    g_netBlockMsTotal += rttMs;
    noteNetResult(false, rttMs);

    Serial.printf("[CHK] FAIL: %s (http=%d rtt=%lums)\n", why, httpCode, (unsigned long)rttMs);
    if (detail.length()) {
      Serial.print("[CHK] detail: ");
      Serial.println(detail);
    }

    if (!quiet) {
      String l1 = "HTTP:" + String(httpCode);
      String l2 = "RTT:" + String((unsigned long)rttMs) + "ms";
      String l3 = why;
      if (l3.length() > 15) l3 = l3.substring(0, 15);
      showStatusScreen("CHECKIN", l1, l2, l3);
      qDelay(false, 900);
    }
    return false;
  };

  auto sanitizeSnippet = [](String s, size_t maxLen = 280) -> String {
    s.replace("\r", " ");
    s.replace("\n", " ");
    s.trim();
    if (s.length() > maxLen) s = s.substring(0, maxLen) + "...";
    return s;
  };

  if (netBackoffActive()) {
    Serial.println("[CHK] Backoff active -> skip");
    return false;
  }

  if (WiFi.status() != WL_CONNECTED) {
    return fail("wifi_disconnected", -1000, 0);
  }

  Serial.println("\n[CHK] checkInAndUpdateFromServer() start");
  Serial.print("[CHK] POST URL: ");
  Serial.println(checkinUrl);

  if (!quiet) {
    showStatusScreen("CHECKIN", "CONTACTING", "SERVER");
    qDelay(false, 50);
  }

  // -----------------------
  // Build request payload
  // -----------------------
  String body;
  {
    uint64_t mac = ESP.getEfuseMac();
    uint32_t hi = (uint32_t)(mac >> 32);
    uint32_t lo = (uint32_t)(mac & 0xFFFFFFFF);

    char hardware_id[13];
    snprintf(hardware_id, sizeof(hardware_id), "%04X%08X", (hi & 0xFFFF), lo);

    StaticJsonDocument<1536> req;
    req["hardware_id"] = hardware_id;
    req["tag"] = g_animTag;
    req["bin_sha256"] = g_binSha256;
    req["mac_address"] = WiFi.macAddress();
    req["fw_version"] = "AuroraDisplay-WeatherClk";
    req["free_fs"] = (int)(LittleFS.totalBytes() - LittleFS.usedBytes());

    JsonObject dbg = req.createNestedObject("debug");
    dbg["heap_free"] = (int)ESP.getFreeHeap();
    dbg["heap_min"] = (int)ESP.getMinFreeHeap();
    dbg["heap_largest"] = (int)heap_caps_get_largest_free_block(MALLOC_CAP_8BIT);
    dbg["psram_free"] = (int)ESP.getFreePsram();
    dbg["wifi_status"] = (int)WiFi.status();
    dbg["wifi_rssi"] = (WiFi.status() == WL_CONNECTED) ? WiFi.RSSI() : 0;
    dbg["uptime_ms"] = (uint32_t)millis();
    dbg["loop_max_ms"] = g_loopMaxMs;
    dbg["wx_http"] = lastWeatherHttpCode;
    dbg["fc_http"] = lastForecastHttpCode;
    dbg["wx_rtt_ms"] = lastWeatherFetchMs;
    dbg["fc_rtt_ms"] = lastForecastFetchMs;
    dbg["chk_http"] = g_lastCheckinHttpCode;
    dbg["chk_rtt_ms"] = g_lastCheckinRttMs;
    dbg["anim_playing"] = adAnim.playing ? 1 : 0;
    dbg["anim_frames"] = adAnim.frameCount;
    dbg["anim_fd_ms"] = adAnim.frameDelayMs;
    dbg["net_block_ms"] = g_lastNetBlockMs;
    dbg["net_block_total_ms"] = g_netBlockMsTotal;
    dbg["net_fail_streak"] = g_netFailStreak;
    dbg["net_backoff_remain_ms"] = netBackoffActive()
                                     ? (uint32_t)(g_netBackoffUntilMs - millis())
                                     : 0;

    serializeJson(req, body);
    Serial.print("[CHK] body bytes: ");
    Serial.println(body.length());
  }

  // -----------------------
  // HTTP with retries
  // -----------------------
  const int maxAttempts = 3;  // 1 + up to 2 retries
  int lastCode = -9999;
  String lastErr;
  String lastRespSnippet;
  uint32_t lastRtt = 0;
  String respBody;

  for (int attempt = 1; attempt <= maxAttempts; ++attempt) {
    HTTPClient http;
    http.setReuse(false);
    http.setFollowRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS);
    http.setConnectTimeout(1500);
    http.setTimeout(3500);  // give Flask a bit more time than 1200ms

    static WiFiClientSecure chkSecure;
    static WiFiClient chkPlain;

    bool beginOk = false;
    if (checkinUrl.startsWith("https://")) {
      chkSecure.setInsecure();
      chkSecure.setHandshakeTimeout(30);
      chkSecure.setTimeout(4);
      beginOk = http.begin(chkSecure, checkinUrl);
    } else {
      chkPlain.setTimeout(4);
      beginOk = http.begin(chkPlain, checkinUrl);
    }

    if (!beginOk) {
      lastCode = -1;
      lastErr = "http.begin failed";
      Serial.printf("[CHK] attempt %d/%d begin failed\n", attempt, maxAttempts);
      http.end();

      if (attempt < maxAttempts) {
        delay(120 + (uint32_t)(esp_random() % 180));
        continue;
      }
      return fail("begin_failed", lastCode, 0, lastErr);
    }

    http.addHeader("Content-Type", "application/json");
    http.addHeader("Accept", "application/json");

    uint32_t t0 = millis();
    int code = http.POST((uint8_t*)body.c_str(), body.length());
    uint32_t rtt = millis() - t0;

    lastCode = code;
    lastRtt = rtt;
    g_lastCheckinHttpCode = code;
    g_lastCheckinRttMs = rtt;

    Serial.printf("[CHK] attempt %d/%d status=%d rtt=%lums\n",
                  attempt, maxAttempts, code, (unsigned long)rtt);

    // Capture body even on non-200 (super important for 500 debugging)
    String bodyMaybe = http.getString();
    if (bodyMaybe.length()) {
      lastRespSnippet = sanitizeSnippet(bodyMaybe, 320);
      Serial.print("[CHK] resp snippet: ");
      Serial.println(lastRespSnippet);
    } else {
      lastRespSnippet = "";
      Serial.println("[CHK] resp snippet: <empty>");
    }

    if (code == HTTP_CODE_OK) {
      respBody = bodyMaybe;
      http.end();
      // success path exits retry loop
      break;
    }

    lastErr = HTTPClient::errorToString(code);

    bool retryable =
      (code < 0) ||                                     // transport errors
      (code == 408) ||                                  // timeout
      (code == 425) || (code == 429) || (code >= 500);  // server transient class

    http.end();

    if (attempt < maxAttempts && retryable) {
      uint32_t backoffMs = (uint32_t)(150 * attempt) + (uint32_t)(esp_random() % 200);
      Serial.printf("[CHK] retrying in %lums (retryable status)\n", (unsigned long)backoffMs);
      delay(backoffMs);
      continue;
    }

    // non-retryable or out of retries
    String detail = lastErr;
    if (lastRespSnippet.length()) detail += " | " + lastRespSnippet;
    return fail("post_failed", code, rtt, detail);
  }

  // Must have a 200 payload by here
  if (respBody.isEmpty()) {
    return fail("empty_200_body", lastCode, lastRtt, lastErr);
  }





  // -----------------------
  // Parse response
  // -----------------------
  DynamicJsonDocument resp(6144);

  DeserializationError jerr = deserializeJson(resp, respBody);
  if (jerr) {
    String detail = String("json_parse: ") + jerr.c_str();
    if (lastRespSnippet.length()) detail += " | " + lastRespSnippet;
    return fail("json_invalid", lastCode, lastRtt, detail);
  }




  bool okFlag = resp["ok"] | false;

  if (!okFlag) {
    String msg = resp["error"] | resp["message"] | "ok_false";
    return fail("server_rejected", lastCode, lastRtt, msg);
  }



  //new

  const char* pairingStateC = resp["pairing"]["state"] | "";
  String pairingState = String(pairingStateC);

  g_lastPairSuccess = (pairingState == "paired");

  const char* fnC = resp["pairing"]["friendly_name"] | "";
  const char* emC = resp["pairing"]["owner_email"] | "";

  g_lastPairFriendlyName = String(fnC);
  g_lastPairOwnerEmail = String(emC);
  g_lastPairFriendlyName.trim();
  g_lastPairOwnerEmail.trim();


  // Pairing info (if present)
  bool pairingPending = resp["pairing"]["pending"] | false;
  String pairCode = String((const char*)(resp["pairing"]["code"] | ""));
  pairCode.trim();

  g_lastCheckinHadPairing = pairingPending && pairCode.length() > 0;
  g_lastPairCode = g_lastCheckinHadPairing ? pairCode : "";

  // If server says we're paired and there is no pending code, force-exit any local pairing mode/poll.
  if (pairingState == "paired" && !pairingPending) {
    // clear anything your UI/poll loop checks
    g_lastCheckinHadPairing = false;
    g_lastPairCode = "";

    // IMPORTANT: also clear your "pair poll" enable flag or UI mode if you have one.
    // Examples (use the real ones in your codebase):
    // g_pairPollEnabled = false;
    // g_pairingActive = false;
    // g_uiMode = UI_WEATHER;
  }

  g_lastCheckinOk = true;

  Serial.printf("[PAIR] pending=%d code='%s' state='%s'\n",
                pairingPending ? 1 : 0,
                pairCode.c_str(),
                pairingStateC);

  Serial.printf("[PAIR] hadPairing=%d lastPairCode='%s'\n",
                g_lastCheckinHadPairing ? 1 : 0,
                g_lastPairCode.c_str());

  // -----------------------
  // Apply tag if returned
  // -----------------------
  const char* newTag = resp["tag"] | "";
  if (newTag && *newTag) {
    String clean = cleanTagFromString(String(newTag));
    if (clean.length()) {
      strncpy(animTagBuf, clean.c_str(), sizeof(animTagBuf));
      animTagBuf[sizeof(animTagBuf) - 1] = '\0';
      p_animTag.setValue(animTagBuf, 17);
      g_animTag = clean;
      applyTagAndPaths(g_animTag);
    }
  }

  bool wantBin = resp["action"]["download_bin"] | false;
  if (!wantBin) {
    noteNetResult(true, millis() - fnStartMs);
    Serial.printf("[CHK] OK: no update, total=%lums\n", (unsigned long)(millis() - fnStartMs));
    if (!quiet) {
      showStatusScreen("CHECK IN", "NO UPDATE", "OK");
      qDelay(false, 3000);
    }
    return true;
  }

  const char* binUrl = resp["bin"]["url"] | "";
  size_t expectedSize = resp["bin"]["size"] | 0;
  const char* newSha = resp["bin"]["sha256"] | "";

// ---- JSON config timeline metadata (optional) ----
const char* jsonUrl = resp["json"]["url"] | "";
size_t jsonExpectedSize = resp["json"]["size"] | 0;
bool hasJson = (jsonUrl && *jsonUrl);

  if (!binUrl || !*binUrl) {
    return fail("missing_bin_url", lastCode, lastRtt);
  }

  if (!quiet) {
    showStatusScreen("CHECKIN", "UPDATE", "DOWNLOADING");
    qDelay(false, 120);
  }

  String finalPath = (adAnim.path.length() && adAnim.path[0] == '/') ? adAnim.path : "/ryu.bin";

  cleanupStaleTemp(finalPath);

  uint32_t dlStart = millis();
  bool dlOk = downloadToTempFile(String(binUrl), finalPath, expectedSize, 15000, true, g_animTag);
  uint32_t dlMs = millis() - dlStart;

  if (!dlOk) {
    return fail("download_failed", lastCode, dlMs);
  }

  uint32_t cmStart = millis();
  bool commitOk = commitTempFile(finalPath);
  uint32_t cmMs = millis() - cmStart;

  if (!commitOk) {
    return fail("commit_failed", lastCode, cmMs);
  }


// -----------------------
// Download + commit JSON (optional)
// -----------------------
if (hasJson) {
  // Optional but recommended (mirrors your old logic)
  // If you don't have these helpers in this codebase, you can remove them and keep cleanupStaleTemp().
  recoverTempAndBackup(g_tagJsonPath);
  cleanupStaleTemp(g_tagJsonPath);

  uint32_t jdlStart = millis();
  bool jdlOk = downloadToTempFile(String(jsonUrl), g_tagJsonPath, jsonExpectedSize, 15000, true, g_animTag);
  uint32_t jdlMs = millis() - jdlStart;

  if (!jdlOk) {
    return fail("download_json_failed", lastCode, jdlMs);
  }

  uint32_t jcmStart = millis();
  bool jcmOk = commitTempFile(g_tagJsonPath);
  uint32_t jcmMs = millis() - jcmStart;

  if (!jcmOk) {
    return fail("commit_json_failed", lastCode, jcmMs);
  }
} else {
  Serial.println("[CHK] No json.url provided; keeping existing/default config.");
}


  if (newSha && *newSha) g_binSha256 = String(newSha);

  
  saveConfig();

  // Reload animation
  stopAnim(adAnim);
  startAnim(adAnim);

  noteNetResult(true, millis() - fnStartMs);

  Serial.printf("[CHK] SUCCESS total=%lums download=%lums commit=%lums\n",
                (unsigned long)(millis() - fnStartMs),
                (unsigned long)dlMs,
                (unsigned long)cmMs);

  if (!quiet) {
    showStatusScreen("CHECKIN", "UPDATE OK", "APPLIED");
    qDelay(false, 450);
  }

  return true;
}




// =====================================================
// OPTIONAL: two convenience wrappers (quiet vs loud)
// Paste wherever you like (same area as deviceCheckinNow)
// =====================================================

bool deviceCheckinLoud(const char* reason = "manual_loud") {
  // If you want a small spam guard:
  // if (!deviceCheckinAllowedNow(millis(), 5000)) return false;
  return deviceCheckinNow(false, reason);
}

bool deviceCheckinQuiet(const char* reason = "manual_quiet") {
  // if (!deviceCheckinAllowedNow(millis(), 5000)) return false;
  return deviceCheckinNow(true, reason);
}



// =====================================================
// DEVICE-INITIATED CHECK-IN TRIGGERS (manual calls)
// Paste this near your CHECK-IN + UPDATE section (below checkInAndUpdateFromServer is perfect)
// =====================================================

bool deviceCheckinNow(bool quiet, const char* reason) {
  uint32_t now = millis();

  Serial.println();
  Serial.println("[DEVCHK] ===== deviceCheckinNow() =====");
  Serial.printf("[DEVCHK] reason=%s quiet=%d\n", reason ? reason : "null", quiet ? 1 : 0);

  // Add the simple manual/rapid-trigger limiter from your other version
  if (!deviceCheckinAllowedNow(now, 5000)) {
    Serial.println("[DEVCHK] manual rate-limited");
    return false;
  }

  // Safety gates
  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("[DEVCHK] WiFi not connected");
    g_lastCheckinHttpCode = 0;
    g_lastCheckinRttMs = 0;

    if (!quiet) deviceShowCheckinResultOverlay(false, 0, 0, 1600);
    return false;
  }

  if (netBackoffActive()) {
    uint32_t remain = (uint32_t)(g_netBackoffUntilMs - now);
    Serial.printf("[DEVCHK] Backoff active, remaining=%ums\n", (unsigned)remain);

    if (!quiet) {
      showStatusScreen("CHECKIN", "BACKOFF", "WAIT", String(remain) + "ms");
      g_btnMsgUntilMs = millis() + 1600;
      g_btnOverlayActive = true;
      g_btnNeedsFullRedraw = true;
    }
    return false;
  }

  if (!canDoNetworkNow(now)) {
    Serial.println("[DEVCHK] Skipped, canDoNetworkNow() returned false");
    if (!quiet) {
      showStatusScreen("CHECKIN", "SKIPPED", "BUSY LOOP");
      g_btnMsgUntilMs = millis() + 1400;
      g_btnOverlayActive = true;
      g_btnNeedsFullRedraw = true;
    }
    return false;
  }

  String url = buildCheckinUrl();
  Serial.print("[DEVCHK] url=");
  Serial.println(url);

  uint32_t t0 = millis();
  bool ok = checkInAndUpdateFromServer(url, quiet);
  uint32_t dt = millis() - t0;

  // Keep diagnostics coherent
  if (g_lastCheckinRttMs == 0) g_lastCheckinRttMs = dt;
  g_lastCheckinMs = millis();

  Serial.printf("[DEVCHK] done ok=%d http=%d rtt=%ums\n",
                ok ? 1 : 0, g_lastCheckinHttpCode, (unsigned)g_lastCheckinRttMs);

  if (!quiet) {
    deviceShowCheckinResultOverlay(ok, g_lastCheckinHttpCode, g_lastCheckinRttMs, 1800);
  }

  // Restore weather on next pass if needed
  if (g_uiMode == UI_WEATHER) {
    screenDrawnOnce = false;
  }

  return ok;
}

// Legacy alias used by button handler – simple wrapper.
bool doManualCheckin(bool quiet) {
  // You can change "button" to "manual" or whatever label you like for logging.
  return deviceCheckinNow(quiet, "button");
}

static void doManualCheckin_OLD(bool quiet) {
  if (WiFi.status() != WL_CONNECTED) {
    // Optional tiny feedback
    if (!quiet) showStatusScreen("CHECKIN", "WIFI", "NOT CONNECT");
    return;
  }

  // Reset cumulative net timing window if you want "since last checkin"
  g_netBlockMsTotal = 0;

  String url = buildCheckinUrl();
  bool ok = checkInAndUpdateFromServer(url, quiet);

  // Optional non-quiet confirmation
  if (!quiet) {
    if (ok) showStatusScreen("CHECKIN", "DONE", "OK");
    else showStatusScreen("CHECKIN", "DONE", "FAIL");
  }
}


bool deviceCheckinAllowedNow(uint32_t nowMs, uint32_t minGapMs) {
  if ((uint32_t)(nowMs - g_lastManualCheckinMs) < minGapMs) {
    return false;
  }
  g_lastManualCheckinMs = nowMs;
  return true;
}


static void exitPairFlowToWeather() {
  g_pairFlow = PAIRFLOW_OFF;

  g_btnOverlayActive = false;
  g_btnMsgUntilMs = 0;
  g_btnNeedsFullRedraw = true;

  // Return to weather UI
  g_uiMode = UI_WEATHER;
  if (weatherReady) {
    WRAP_DISPLAY("clearScreen", dma_display->clearScreen());
    WRAP_DISPLAY("drawWeatherDataAndClock", drawWeatherDataAndClock());
    screenDrawnOnce = true;
    WRAP_BLOCK("initCityScroll", initCityScroll(globalCityName));
    g_weatherPhaseStartMs = millis();
  } else {
    WRAP_DISPLAY("fillRect_black_full", dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, UI_BLACK));
    screenDrawnOnce = false;
  }
}

static void enterPairFlowWaitCode() {
  uint32_t now = millis();
  g_pairFlow = PAIRFLOW_WAIT_CODE;
  g_pairPhaseStartMs = now;
  g_pairPhaseEndMs = now + PAIR_PHASE_MS;
  g_pairNextCheckinMs = now;  // immediate

  g_btnOverlayActive = true;
  g_btnMsgUntilMs = g_pairPhaseEndMs;
  g_btnNeedsFullRedraw = true;

  showStatusScreen("PAIRING", "WAIT FOR CODE", "CHECKIN 10S", "TIME 03:00");
}

static void enterPairFlowWaitSuccess() {
  uint32_t now = millis();
  g_pairFlow = PAIRFLOW_WAIT_SUCCESS;
  g_pairPhaseStartMs = now;
  g_pairPhaseEndMs = now + PAIR_PHASE_MS;
  g_pairNextCheckinMs = now;  // immediate

  g_btnOverlayActive = true;
  g_btnMsgUntilMs = g_pairPhaseEndMs;
  g_btnNeedsFullRedraw = true;

  showStatusScreen("PAIR READY", "CODE:" + g_lastPairCode, "WAIT CONFIRM", "TIME 03:00");
}

static void drawPairCountdownLine4() {
  uint32_t now = millis();
  int32_t remaining = (int32_t)(g_pairPhaseEndMs - now);
  if (remaining < 0) remaining = 0;

  uint32_t sec = (uint32_t)remaining / 1000UL;
  uint32_t mm = sec / 60UL;
  uint32_t ss = sec % 60UL;

  char buf[16];
  snprintf(buf, sizeof(buf), "TIME %02lu:%02lu", (unsigned long)mm, (unsigned long)ss);

  // If you have a helper to update only line 4, use it.
  // Otherwise, redraw full status screen.
  if (g_pairFlow == PAIRFLOW_WAIT_CODE) {
    showStatusScreen("PAIRING", "WAIT CODE", "CHECKIN 10S", String(buf));
  } else if (g_pairFlow == PAIRFLOW_WAIT_SUCCESS) {
    showStatusScreen("PAIR READY", "CODE:" + g_lastPairCode, "WAIT CONFIRM", String(buf));
  }
}

static uint32_t g_lastCountdownDrawMs = 0;

void handlePairFlowLoop() {
  if (g_pairFlow == PAIRFLOW_OFF) return;

  uint32_t now = millis();
  // If server says we're already paired, pairing flow should end immediately.
  if (g_lastPairSuccess && !g_lastCheckinHadPairing && g_lastPairCode.length() == 0) {
    g_pairFlow = PAIRFLOW_OFF;
    exitPairFlowToWeather();
    return;
  }


  // If we are in the "show paired briefly" hold, wait then exit to weather
  if (g_pairShowPairedActive) {
    if ((int32_t)(now - g_pairShowPairedUntilMs) >= 0) {
      g_pairShowPairedActive = false;
      exitPairFlowToWeather();
    }
    return;
  }


  // Timeout handling
  if ((int32_t)(now - g_pairPhaseEndMs) >= 0) {
    // Phase timed out
    exitPairFlowToWeather();
    return;
  }

  // Draw countdown roughly once per second
  if (now - g_lastCountdownDrawMs >= 1000UL) {
    g_lastCountdownDrawMs = now;
    drawPairCountdownLine4();
  }

  // Poll check-in every 10 seconds
  if ((int32_t)(now - g_pairNextCheckinMs) >= 0) {
    g_pairNextCheckinMs = now + PAIR_POLL_MS;

    // Call your check-in function in "quiet" mode so it does not restart pairing flow
    // and does not spam overlays. This must NOT call deviceShowCheckinResultOverlay with ms > 0.
    deviceCheckinQuiet("pair_poll");
  }

  // Phase transitions based on latest parsed check-in results
  if (g_pairFlow == PAIRFLOW_WAIT_CODE) {
    if (g_lastCheckinHadPairing && g_lastPairCode.length() > 0) {
      enterPairFlowWaitSuccess();
      return;
    }
  } else if (g_pairFlow == PAIRFLOW_WAIT_SUCCESS) {
    if (g_lastPairSuccess) {
      String fn = g_lastPairFriendlyName;
      fn.trim();
      if (fn.length() == 0) fn = "DEVICE";

      // Show "PAIRED" with friendly name and tell the user we are returning
      showStatusScreen("PAIRED", fn, "RETURNING", " ");

      // Stop the pairing state machine. We are just showing the success screen now.

      // Non-blocking "delay" for the success screen
      g_pairShowPairedActive = true;
      g_pairShowPairedUntilMs = now + 5000UL;  // 5 seconds

      g_pairFlow = PAIRFLOW_OFF;

      return;
    }
  }
}


// =====================================================
// SETUP / LOOP
// =====================================================
void setup() {
  // useHardcodedWiFi = false;  // Optional override while testing

  // Default animation path before config/tag load
  adAnim.path = "/ryu.bin";

  // Core startup
  WiFi.mode(WIFI_STA);
  Serial.begin(115200);
  Serial.setDebugOutput(true);
  delay(1000);
  Serial.println("\n Starting");

  // Hardware init
  setupButtonGPIO();
  setupDisplay();

  // Show hardware ID splash (long display for commissioning/debug)
  showHardwareIdSplash(10000);

  // Default animation timings
  adAnim.showDurationMs = 10000;
  adAnim.frameDelayMs = 120;

  // Clear panel and show startup status
  dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, UI_BLACK);
  dma_display->clearScreen();

  showStatusScreen("STARTING", "LOADING", "SETTINGS");
  delay(1000);

  // =====================================================
  // Filesystem init (LittleFS)
  // =====================================================
  bool fsOK = LittleFS.begin();

  Serial.println("LittleFS contents:");
  File root = LittleFS.open("/");
  File f = root.openNextFile();
  while (f) {
    Serial.printf("  %s  size=%u\n", f.name(), (unsigned)f.size());
    f = root.openNextFile();
  }

  if (!fsOK) {
    Serial.println("Mounting FS failed, formatting...");
    if (!LittleFS.format()) {
      Serial.println("Filesystem formatting failed");
      return;
    }
    fsOK = LittleFS.begin();
    if (!fsOK) {
      Serial.println("Mounting FS failed after formatting");
      return;
    }
  }
  Serial.println("Filesystem mounted OK");

  // Load persisted config; if missing, fall back to default tag/path behavior
  bool loaded = loadConfig();
  if (!loaded) {
    applyTagAndPaths(g_animTag);
  }

  // Apply persisted/default brightness
  applyBrightness();

  // Button reset prompt
  showStatusScreen("To RESET", "HOLD BUTTON", "FOR 5 ", "SECONDS");
  delay(3000);

  // =====================================================
  // Wi-Fi connect path
  // =====================================================
  if (useHardcodedWiFi) {
    // Hardcoded credentials flow
    WiFi.begin(hardcodedSSID, hardcodedPassword);
    Serial.print("Connecting to WiFi: ");
    Serial.println(hardcodedSSID);

    unsigned long startTime = millis();
    while (WiFi.status() != WL_CONNECTED && millis() - startTime < 10000) {
      delay(500);
      Serial.print(".");
    }

    if (WiFi.status() == WL_CONNECTED) {
      Serial.println("\nConnected using hardcoded credentials!");
      Serial.print("IP Address: ");
      Serial.println(WiFi.localIP());
    } else {
      Serial.println("\nFailed to connect using hardcoded credentials.");
      ESP.restart();
    }
  } else {
    // WiFiManager portal flow
    WiFiManager wm;

    // Allow button-driven reset behavior
    checkButton(wm);

    // On-matrix portal instructions
    dma_display->clearScreen();

    String ssid = "WeatherClk";
    String pass = "ResetMe123";
    String ip = "192.168.4.1";

    drawCentered3x5(0, "WIFI SETUP", UI_WHITE, UI_BLACK);
    drawString3x5(0, 7, "SSID:" + ssid, UI_WHITE, UI_BLACK);
    drawString3x5(0, 14, "PASS:" + pass, UI_WHITE, UI_BLACK);
    drawCentered3x5(21, "IP:" + ip, UI_WHITE, UI_BLACK);

    // Portal visual styling
    wm.setTitle("www.aururadisplay.ca Setup");
    wm.setCustomHeadElement(
      "<style>"
      "body{font-family:Arial!important;}"
      "h1,h2{letter-spacing:0.5px;}"
      ".msg{border-radius:10px!important;}"
      "input,select,button{border-radius:10px!important;}"
      "</style>");

    // Branded header block in portal
    WiFiManagerParameter p_brand(
      "<div style='padding:12px; margin:10px 0; border-radius:10px;'"
      "background:#111; color:#fff; font-family:Arial;'>"
      "<div style='font-size:18px; font-weight:700;'>Testing 2</div>"
      "<div style='font-size:12px; opacity:.85; margin-top:4px;'>"
      "Wi-Fi • City • Sleep • Brightness</div>"
      "</div>");

    // Portal fields (in display order)
    wm.addParameter(&p_brand);

    wm.addParameter(&p_instructions);
    wm.addParameter(&custom_parameter);

    wm.addParameter(&p_sleepInfo);
    wm.addParameter(&p_sleepEnabled);
    wm.addParameter(&p_sleepStart);
    wm.addParameter(&p_sleepEnd);

    wm.addParameter(&p_brightnessInfo);
    wm.addParameter(&p_brightness);

    wm.addParameter(&p_animTag);

    wm.addParameter(&p_updateInfo);
    wm.addParameter(&p_weatherUpdateMins);
    wm.addParameter(&p_checkinUpdateMins);

    wm.addParameter(&p_weatherModeSecs);
    wm.addParameter(&p_animModeSecs);
    wm.addParameter(&p_clockModeSecs);  // Keep if clock timed mode is used
    wm.addParameter(&p_adAnimSecs);     // Keep if ad timing remains separate

    // Persist config callback
    wm.setSaveConfigCallback(saveConfigCallback);

    // Portal behavior
    wm.setConnectTimeout(180);
    wm.setDebugOutput(true);

    // Start AP/captive portal and attempt connection
    bool res = wm.autoConnect("WeatherClk", "ResetMe123");

    if (!res) {
      Serial.println("Failed to connect and hit timeout");
      dma_display->clearScreen();
      showStatusScreen("WIFI", "FAILED", "RESTARTING");
      delay(3000);
    } else {
      Serial.println("Connected to WiFi");
      showStatusScreen("WIFI", "CONNECTED");
      delay(3000);
    }
  }

  // =====================================================
  // NTP sync
  // =====================================================
  showStatusScreen("TIME", "SYNCING", "NTP");
  delay(250);
  timeClient.begin();

  uint32_t t0 = millis();
  bool ok = timeClient.update();
  Serial.printf("[NTP] initial update ok=%d dt=%lums\n", ok, millis() - t0);

  // Start periodic NTP interval from now
  lastNtpMs = millis();

  // =====================================================
  // Initial weather/forecast fetch and first render
  // =====================================================
  showStatusScreen("FETCH", "FORECAST", "{{" + weatherCity + "}}");
  delay(2000);
  forecastReady = updateForecastAndStore();

  showStatusScreen("FETCH", "WEATHER", "{{" + weatherCity + "}}");
  delay(250);
  weatherReady = updateWeatherDisplay();

  showStatusScreen("UPDATING", "WEATHER FOR", "{{" + weatherCity + "}}", "PLEASE WAIT");
  delay(2000);

  // Kept as-is: second weather refresh
  updateWeatherDisplay();

  showStatusScreen("FETCH", "FORECAST", "{{" + weatherCity + "}}");
  delay(2000);

  dma_display->clearScreen();
  drawWeatherDataAndClock();
  g_weatherPhaseStartMs = millis();  // Start weather phase timer

  // =====================================================
  // Initial backend check-in
  // =====================================================
  Serial.println("[CHECKIN] Asking server if update needed...");
  showStatusScreen("CHECKIN", "SERVER", "{{OK}}");
  delay(2000);

  // Loud check-in in setup (UI + debug pacing preserved)
  //  checkInAndUpdateFromServer("http://www.auroradisplay.ca/api/checkin", false);
  checkInAndUpdateFromServer(buildCheckinUrl(), false);


  // Boot sequence complete
  g_bootInProgress = false;

  // Initialize loop timers
  g_lastWeatherUpdateMs = millis();
  g_lastCheckinMs = millis();

  // Draw final starting screen state
  dma_display->clearScreen();
  drawWeatherDataAndClock();
  screenDrawnOnce = true;

  // Respect current UI mode
  if (g_uiMode == UI_ANIM) {
    if (!adAnim.playing) startAnim(adAnim);
  } else {
    adAnim.playing = false;  // Ensure startup lands on weather
    g_weatherPhaseStartMs = millis();
    drawWeatherDataAndClock();
    screenDrawnOnce = true;
  }

  // Wi-Fi resilience settings
  WiFi.setAutoReconnect(true);
  WiFi.persistent(true);
}





void loop() {
  uint32_t now = millis();

  handlePairFlowLoop();

  // If pairing flow is active, you likely want to stop the normal weather loop from drawing over it.
  if (g_pairFlow != PAIRFLOW_OFF) {
    return;
  }

  static uint32_t g_lastLoopStamp = 0;
  if (g_lastLoopStamp != 0) {
    uint32_t dt = now - g_lastLoopStamp;
    if (dt > g_loopMaxMs) g_loopMaxMs = dt;
  }
  g_lastLoopStamp = now;


  //button
  uint32_t t0 = millis();

  //uint32_t now = millis();
  //serviceButtonAnytime(now);  // Manual check-in trigger (1s hold + release)
  serviceButtonHoldUI(now);  // Hold UI pages + mode cycling
  serviceUiModeAnytime(now);



  // Auto-return to weather when a temporary mode expires
  if (g_uiMode != UI_WEATHER && g_uiModeUntilMs != 0 && (int32_t)(now - g_uiModeUntilMs) >= 0) {
    g_uiMode = UI_WEATHER;
    g_uiModeUntilMs = 0;
    g_btnOverlayActive = true;
    g_btnNeedsFullRedraw = true;
  }

  static uint32_t lastHealth = 0;
  if (millis() - lastHealth > 60000) {
    lastHealth = millis();

    Serial.printf(
      "[HEALTH] heap=%u largest=%u min=%u wifi=%d rssi=%d wx=%d fc=%d anim=%d fpsDelay=%u "
      "loopMax=%u worst=%s(%u) dispWorst=%s(%u) netLast=%u netTotal=%u failStreak=%u\n",
      (unsigned)ESP.getFreeHeap(),
      (unsigned)heap_caps_get_largest_free_block(MALLOC_CAP_8BIT),
      (unsigned)ESP.getMinFreeHeap(),
      (int)WiFi.status(),
      (WiFi.status() == WL_CONNECTED) ? WiFi.RSSI() : 0,
      lastWeatherHttpCode,
      lastForecastHttpCode,
      adAnim.playing ? 1 : 0,
      (unsigned)adAnim.frameDelayMs,
      (unsigned)g_loopMaxMs,
      g_worstBlockName, (unsigned)g_worstBlockMs,              // char[]
      g_worstDisplayName.c_str(), (unsigned)g_worstDisplayMs,  // String -> c_str()
      (unsigned)g_lastNetBlockMs,
      (unsigned)g_netBlockMsTotal,
      (unsigned)g_netFailStreak);

    // reset perf window stats
    g_loopMaxMs = 0;
    g_worstBlockMs = 0;
    g_worstDisplayMs = 0;
    strlcpy(g_worstBlockName, "none", sizeof(g_worstBlockName));
    g_worstDisplayName = "none";
  }



  // Pairing success 'PAIRED' screen gate
  if (g_pairShowPairedActive) {
    uint32_t now = millis();

    // Still within the "show paired screen" window, do nothing,
    // leave the last frame frozen.
    if ((int32_t)(now - g_pairShowPairedUntilMs) < 0) {
      return;
    }

    // Time window expired, exit pairing flow and go back to weather.
    g_pairShowPairedActive = false;
    g_pairSuccessPhase = false;
    g_pairCountdownActive = false;

    exitPairFlowToWeather();
    return;
  }

  // Overlay gate
  if (g_btnOverlayActive) {

    // If we are in the 3 minute pairing countdown, update the timer text
    if (g_pairCountdownActive) {
      int32_t remainingMs = (int32_t)(g_btnMsgUntilMs - now);
      if (remainingMs < 0) remainingMs = 0;

      uint16_t secs = (uint16_t)(remainingMs / 1000);
      if (secs != g_pairCountdownLastSeconds) {
        g_pairCountdownLastSeconds = secs;

        uint8_t mm = secs / 60;
        uint8_t ss = secs % 60;

        String line4 = "TIME " + String(mm) + ":" + (ss < 10 ? "0" : "") + String(ss);

        // Live countdown screen
        showStatusScreen(
          "PAIR READY",
          "CODE:" + g_lastPairCode,
          "WAITING SERVER",
          line4);
      }
    }

    // Check if overlay lifetime has expired
    bool expired = false;
    if (g_btnMsgUntilMs == 0) {
      expired = true;
    } else if ((int32_t)(now - g_btnMsgUntilMs) >= 0) {
      expired = true;
    }

    if (!expired) {
      // Overlay still active, keep blocking normal UI
      return;
    }

    // At this point, the current overlay "phase" has expired

    // If countdown just finished, move into 5 second SUCCESS phase
    if (g_pairCountdownActive) {
      g_pairCountdownActive = false;
      g_pairCountdownLastSeconds = 0xFFFF;
      g_pairSuccessPhase = true;

      g_btnMsgUntilMs = now + 5000;  // 5 seconds for success screen
      g_btnNeedsFullRedraw = true;

      showStatusScreen(
        "SUCCESS",
        "PAIRING COMPLETE",
        "",
        "OK");

      // Keep overlay active during success phase
      return;
    }

    // If success phase just finished, clear that flag and fall through
    if (g_pairSuccessPhase) {
      g_pairSuccessPhase = false;
    }

    // Fully clear overlay and restore underlying UI
    g_btnOverlayActive = false;

    if (g_btnNeedsFullRedraw) {
      g_btnNeedsFullRedraw = false;

      if (g_uiMode == UI_WEATHER) {
        if (weatherReady) {
          WRAP_DISPLAY("clearScreen", dma_display->clearScreen());
          WRAP_DISPLAY("drawWeatherDataAndClock", drawWeatherDataAndClock());
          screenDrawnOnce = true;
          WRAP_BLOCK("initCityScroll", initCityScroll(globalCityName));
          g_weatherPhaseStartMs = millis();
        } else {
          WRAP_DISPLAY("fillRect_black_full",
                       dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, UI_BLACK));
          screenDrawnOnce = false;
        }
      } else if (g_uiMode == UI_CLOCK) {
        WRAP_DISPLAY("fillRect_black_full",
                     dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, UI_BLACK));
        WRAP_DISPLAY("drawDigitalClock", drawDigitalClock());
      } else if (g_uiMode == UI_ANIM) {
        if (!adAnim.playing) {
          WRAP_BLOCK("startAnim", startAnim(adAnim));
        }
      }
    }
  }

  //WRAP_BLOCK("timeClient.update", timeClient.update());




  int currentHour = timeClient.getHours();
  int currentMinute = timeClient.getMinutes();
  int currentSecond = timeClient.getSeconds();
  int dom = getLocalDayOfMonth();

  bool inDayMode = isInOnWindow(currentHour, g_sleepEnabled, g_sleepStartHour, g_sleepEndHour);
  if (g_uiMode == UI_CLOCK) inDayMode = false;

  // Manual UI overrides
  if (g_uiMode == UI_ANIM) {
    if (!adAnim.playing) {
      WRAP_BLOCK("startAnim", startAnim(adAnim));
      return;
    }
    WRAP_BLOCK("updateAnim", updateAnim(adAnim));
    return;
  }

  if (g_uiMode == UI_CLOCK) {
    static int lastDisplayedMinuteClock = -1;
    if (currentMinute != lastDisplayedMinuteClock) {
      lastDisplayedMinuteClock = currentMinute;
      WRAP_DISPLAY("fillRect_black_full", dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, UI_BLACK));
      WRAP_DISPLAY("drawDigitalClock", drawDigitalClock());
    }
    return;
  }

  // UI_WEATHER
  if (inDayMode) {
    if (g_animMissingNeedsRestore && (int32_t)(now - g_animMissingShowUntilMs) >= 0) {
      g_animMissingNeedsRestore = false;

      if (weatherReady) {
        WRAP_DISPLAY("clearScreen", dma_display->clearScreen());
        WRAP_DISPLAY("drawWeatherDataAndClock", drawWeatherDataAndClock());
        screenDrawnOnce = true;
        WRAP_BLOCK("initCityScroll", initCityScroll(globalCityName));
      } else {
        WRAP_DISPLAY("fillRect_black_full", dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, UI_BLACK));
        screenDrawnOnce = false;
      }
    }

    // Weather/Anim cycle
    if (!adAnim.playing) {
      const uint32_t weatherMs = (uint32_t)g_weatherModeSeconds * 1000UL;
      if (g_weatherPhaseStartMs == 0) g_weatherPhaseStartMs = millis();

      if (weatherMs > 0 && (millis() - g_weatherPhaseStartMs) >= weatherMs) {
        adAnim.showDurationMs = (uint32_t)g_animModeSeconds * 1000UL;

        if (g_animMissing) {
          g_weatherPhaseStartMs = millis();
          WRAP_BLOCK("showNoAnimMessage", showNoAnimMessage());
          return;
        }

        WRAP_BLOCK("startAnim", startAnim(adAnim));
        return;
      }
    }

    if (adAnim.playing) {
      WRAP_BLOCK("updateAnim", updateAnim(adAnim));
      return;
    }

    if (g_demoMode) {
      WRAP_BLOCK("handleDemoMode", handleDemoMode());

      if ((int32_t)(millis() - g_demoHoldUntilMs) >= 0) {
        WRAP_BLOCK("updateScrollingText", updateScrollingText());
        WRAP_BLOCK("updateCityScrollBand", updateCityScrollBand(globalCityName));
      }
      return;
    }

    if (!screenDrawnOnce || !weatherReady) {
      WRAP_DISPLAY("fillRect_updating_band", dma_display->fillRect(0, 26, 64, 6, dma_display->color565(0, 0, 0)));
      WRAP_DISPLAY("drawString_UPDATING", drawString3x5(0, 27, "UPDATING...", UI_WHITE, UI_BLACK));

      if (millis() - lastFetchRetryMs >= FETCH_RETRY_INTERVAL_MS) {
        lastFetchRetryMs = millis();
        Serial.println("Fetch status: " + lastFetchNote);

        if (!forecastReady) {
          WRAP_BLOCK("updateForecastAndStore", updateForecastAndStore());
          //Lets service time on forecast
          serviceTime();
        }

        bool okWx = false;
        WRAP_BLOCK_RET_BOOL("updateWeatherDisplay", okWx, updateWeatherDisplay());

        if (screenDrawnOnce) {
          WRAP_BLOCK("initCityScroll", initCityScroll(globalCityName));
        }
      }
      return;
    }

    // Timed updates
    const uint32_t wxEveryMs = (uint32_t)g_weatherUpdateMins * 60UL * 1000UL;
    const uint32_t chkEveryMs = (uint32_t)g_checkinUpdateMins * 60UL * 1000UL;

    // Weather refresh
    if (!adAnim.playing && wxEveryMs > 0 && (millis() - g_lastWeatherUpdateMs) >= wxEveryMs) {
      if (canDoNetworkNow(now)) {
        g_lastWeatherUpdateMs = millis();

        uint32_t tNet = millis();
        bool okWx = false;
        WRAP_BLOCK_RET_BOOL("updateWeatherDisplay", okWx, updateWeatherDisplay());
        g_lastNetBlockMs = millis() - tNet;
        g_netBlockMsTotal += g_lastNetBlockMs;

        if (!okWx) {
          g_netFailStreak = (g_netFailStreak < 8) ? g_netFailStreak + 1 : 8;
          uint32_t backoffMs = 5000UL << (g_netFailStreak > 5 ? 5 : g_netFailStreak);
          g_netBackoffUntilMs = millis() + backoffMs;
        } else {
          g_netFailStreak = 0;
          g_netBackoffUntilMs = 0;
          WRAP_BLOCK("initCityScroll", initCityScroll(globalCityName));
        }
      }
    }

    // Animation check-in refresh
    if (!adAnim.playing && chkEveryMs > 0 && (millis() - g_lastCheckinMs) >= chkEveryMs) {
      if (canDoNetworkNow(now)) {
        g_lastCheckinMs = millis();
        WRAP_BLOCK("checkInAndUpdateFromServer",
                   //checkInAndUpdateFromServer("http://www.auroradisplay.ca/api/checkin", true))
                   checkInAndUpdateFromServer(buildCheckinUrl(), true));
      }
    }

    int slot = -1;
    if (currentHour == FORECAST_HOUR_1) slot = 0;
    else if (currentHour == FORECAST_HOUR_2) slot = 1;

    if (slot != -1 && currentMinute == 0 && currentSecond < FORECAST_WINDOW_SECONDS) {
      bool newDayOrUnknown = (dom == -1) || (dom != lastForecastUpdateDay);
      bool newSlot = (slot != lastForecastUpdateSlot);

      if (newDayOrUnknown || newSlot) {
        if (dom != -1) lastForecastUpdateDay = dom;
        lastForecastUpdateSlot = slot;

        bool fcOk = false;
        WRAP_BLOCK_RET_BOOL("updateForecastAndStore", fcOk, updateForecastAndStore());

        if (fcOk) {
          globalScrollingText = globalDescription + " -- Wind: " + String(globalWindSpeed) + "m/s";
          globalScrollingText += " -- " + forecastString;

          WRAP_DISPLAY("drawWeatherDataAndClock", drawWeatherDataAndClock());
          screenDrawnOnce = true;
          WRAP_BLOCK("initCityScroll", initCityScroll(globalCityName));
        } else {
          lastFetchNote = "FC update fail";
        }
      }
    }

    WRAP_BLOCK("updateScrollingText", updateScrollingText());
    WRAP_BLOCK("updateCityScrollBand", updateCityScrollBand(globalCityName));

  } else {
    static int lastDisplayedMinute = -1;
    if (currentMinute != lastDisplayedMinute) {
      lastDisplayedMinute = currentMinute;
      WRAP_DISPLAY("fillRect_black_full", dma_display->fillRect(0, 0, PANEL_RES_X, PANEL_RES_Y, dma_display->color565(0, 0, 0)));
      WRAP_DISPLAY("drawDigitalClock", drawDigitalClock());
    }
  }


  //button
  uint32_t dt = millis() - t0;
  if (dt > g_loopMaxMs) g_loopMaxMs = dt;
}
