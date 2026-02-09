// DateTime FFI Implementation
// UTC midnight calculation for countdown timer

// | Calculate milliseconds until next UTC midnight
export const calculateMsUntilMidnightUTC = function(nowMs) {
  const now = new Date(nowMs);

  // Create midnight UTC for tomorrow
  const tomorrow = new Date(Date.UTC(
    now.getUTCFullYear(),
    now.getUTCMonth(),
    now.getUTCDate() + 1,  // Tomorrow
    0, 0, 0, 0             // 00:00:00.000 UTC
  ));

  // Return milliseconds UNTIL midnight (difference)
  return tomorrow.getTime() - nowMs;
};

// | Get current time in milliseconds
export const getCurrentTimeMs = function() {
  return Date.now();
};

// | Get current DateTime
export const getCurrentDateTime = function() {
  const now = new Date();
  return fromTimestamp(now.getTime());
};

// | Convert timestamp (milliseconds) to DateTime
export const fromTimestamp = function(timestampMs) {
  const date = new Date(timestampMs);
  // PureScript DateTime uses Data.Date.Month which is 1-indexed (January = 1)
  // JavaScript Date.getUTCMonth() is 0-indexed (January = 0)
  const month = date.getUTCMonth() + 1;

  return {
    date: {
      year: date.getUTCFullYear(),
      month: month,
      day: date.getUTCDate()
    },
    time: {
      hour: date.getUTCHours(),
      minute: date.getUTCMinutes(),
      second: date.getUTCSeconds(),
      millisecond: date.getUTCMilliseconds()
    }
  };
};

// | Parse ISO 8601 DateTime string to DateTime
// | Returns error timestamp if parsing fails
export const fromISOString = function(isoString) {
  const date = new Date(isoString);
  // If parsing failed, return epoch 0 (deterministic error value)
  if (isNaN(date.getTime())) {
    return fromTimestamp(0.0);
  }
  return fromTimestamp(date.getTime());
};

// | Format DateTime as ISO 8601 string
// | Converts PureScript DateTime structure to JavaScript Date, then formats as ISO string
export const toISOString = function(dt) {
  // Extract components from PureScript DateTime structure
  const year = dt.date.year;
  const month = dt.date.month - 1; // JavaScript months are 0-indexed
  const day = dt.date.day;
  const hour = dt.time.hour;
  const minute = dt.time.minute;
  const second = dt.time.second;
  const millisecond = dt.time.millisecond;

  // Create JavaScript Date in UTC
  const date = new Date(Date.UTC(year, month, day, hour, minute, second, millisecond));

  // Format as ISO 8601 string
  return date.toISOString();
};

// | Convert DateTime to timestamp (milliseconds)
// | Converts PureScript DateTime structure to JavaScript Date, then returns milliseconds
export const toTimestamp = function(dt) {
  // Extract components from PureScript DateTime structure
  const year = dt.date.year;
  const month = dt.date.month - 1; // JavaScript months are 0-indexed
  const day = dt.date.day;
  const hour = dt.time.hour;
  const minute = dt.time.minute;
  const second = dt.time.second;
  const millisecond = dt.time.millisecond;

  // Create JavaScript Date in UTC
  const date = new Date(Date.UTC(year, month, day, hour, minute, second, millisecond));

  // Return milliseconds since epoch
  return date.getTime();
};
