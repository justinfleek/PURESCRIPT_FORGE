// DateTime FFI Module
// Provides FFI bindings for DateTime operations and UTC calculations

// Calculate milliseconds until next UTC midnight
export function calculateMsUntilMidnightUTC(nowMs) {
  if (typeof nowMs !== "number" || isNaN(nowMs)) {
    return 0;
  }

  const now = new Date(nowMs);
  const year = now.getUTCFullYear();
  const month = now.getUTCMonth();
  const day = now.getUTCDate();

  // Create next midnight UTC
  const nextMidnight = new Date(Date.UTC(year, month, day + 1, 0, 0, 0, 0));

  return nextMidnight.getTime() - now.getTime();
}

// Get current time in milliseconds
export function getCurrentTimeMs() {
  return Date.now();
}

// Get current DateTime (from milliseconds)
// Returns DateTime object compatible with PureScript Data.DateTime
export function getCurrentDateTime() {
  const now = new Date();
  return fromTimestamp(now.getTime());
}

// Convert timestamp (milliseconds) to DateTime
export function fromTimestamp(timestampMs) {
  const date = new Date(timestampMs);
  
  // Extract UTC components
  const year = date.getUTCFullYear();
  const month = date.getUTCMonth() + 1; // JavaScript months are 0-indexed
  const day = date.getUTCDate();
  const hour = date.getUTCHours();
  const minute = date.getUTCMinutes();
  const second = date.getUTCSeconds();
  const millisecond = date.getUTCMilliseconds();

  // Return object compatible with PureScript Data.DateTime.DateTime
  return {
    date: {
      year,
      month,
      day
    },
    time: {
      hour,
      minute,
      second,
      millisecond
    }
  };
}

// Convert DateTime to timestamp (milliseconds)
export function toTimestamp(dateTime) {
  if (!dateTime || !dateTime.date || !dateTime.time) {
    return 0;
  }

  const { year, month, day } = dateTime.date;
  const { hour, minute, second, millisecond } = dateTime.time;

  // JavaScript Date.UTC uses 0-indexed months
  return Date.UTC(year, month - 1, day, hour, minute, second, millisecond || 0);
}

// Parse ISO 8601 DateTime string to DateTime
export function fromISOString(isoString) {
  if (typeof isoString !== "string") {
    return fromTimestamp(0);
  }

  try {
    const date = new Date(isoString);
    if (isNaN(date.getTime())) {
      return fromTimestamp(0);
    }
    return fromTimestamp(date.getTime());
  } catch (e) {
    return fromTimestamp(0);
  }
}

// Format DateTime as ISO 8601 string
export function toISOString(dateTime) {
  if (!dateTime || !dateTime.date || !dateTime.time) {
    return new Date(0).toISOString();
  }

  const timestamp = toTimestamp(dateTime);
  return new Date(timestamp).toISOString();
}
