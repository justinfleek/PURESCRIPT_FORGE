"use strict";

/**
 * Locale FFI
 * Provides locale utilities
 */

const os = require("os");

// | Get system locale
exports.getSystemLocale = function () {
  const locale = process.env.LANG || process.env.LC_ALL || process.env.LC_MESSAGES || "en-US";
  // Extract language code (e.g., "en_US.UTF-8" -> "en-US")
  return locale.split(".")[0].replace("_", "-");
};

// | Format number for locale
exports.formatNumberForLocale = function (number) {
  return function (locale) {
    try {
      return new Intl.NumberFormat(locale).format(number);
    } catch (error) {
      return String(number);
    }
  };
};

// | Format date for locale
exports.formatDateForLocale = function (timestamp) {
  return function (locale) {
    try {
      const date = new Date(timestamp);
      return new Intl.DateTimeFormat(locale).format(date);
    } catch (error) {
      return date.toISOString();
    }
  };
};
