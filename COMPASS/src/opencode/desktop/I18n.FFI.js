"use strict";

const { Store } = require("@tauri-apps/plugin-store");

/**
 * Desktop I18n FFI
 * Provides locale detection and translation loading
 */

const LOCALES = ["en", "zh", "zht", "ko", "de", "es", "fr", "da", "ja", "pl", "ru", "ar", "no", "br"];

/**
 * Detect locale from navigator
 */
function detectLocale() {
  if (typeof navigator !== "object") return "en";

  const languages = navigator.languages && navigator.languages.length > 0
    ? navigator.languages
    : [navigator.language];

  for (let i = 0; i < languages.length; i++) {
    const language = languages[i];
    if (!language) continue;
    const lower = language.toLowerCase();
    
    if (lower.startsWith("zh")) {
      if (lower.includes("hant")) return "zht";
      return "zh";
    }
    if (lower.startsWith("ko")) return "ko";
    if (lower.startsWith("de")) return "de";
    if (lower.startsWith("es")) return "es";
    if (lower.startsWith("fr")) return "fr";
    if (lower.startsWith("da")) return "da";
    if (lower.startsWith("ja")) return "ja";
    if (lower.startsWith("pl")) return "pl";
    if (lower.startsWith("ru")) return "ru";
    if (lower.startsWith("ar")) return "ar";
    if (lower.startsWith("no") || lower.startsWith("nb") || lower.startsWith("nn")) return "no";
    if (lower.startsWith("pt")) return "br";
  }

  return "en";
}

/**
 * Parse locale from value
 */
function parseLocale(value) {
  if (!value || typeof value !== "string") return null;
  if (LOCALES.includes(value)) return value;
  return null;
}

/**
 * Parse record and extract locale
 */
function pickLocale(value) {
  const direct = parseLocale(value);
  if (direct) return direct;

  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  return parseLocale(value.locale);
}

/**
 * Get current locale
 */
exports.getLocale = function () {
  return detectLocale();
};

/**
 * Set locale
 */
exports.setLocale = function (locale) {
  return function () {
    if (LOCALES.includes(locale)) {
      const store = Store.load("opencode.global.dat");
      store.then(function (s) {
        return s.set("language", JSON.stringify({ locale: locale }));
      }).catch(function () {
        return null;
      });
    }
  };
};

/**
 * Detect locale from navigator
 */
exports.detectLocale = function () {
  return detectLocale();
};

/**
 * Load saved locale from Tauri store
 */
exports.loadSavedLocale = function () {
  return function () {
    return Store.load("opencode.global.dat")
      .then(function (store) {
        return store.get("language").catch(function () {
          return null;
        });
      })
      .then(function (raw) {
        if (!raw || typeof raw !== "string") return null;
        try {
          const value = JSON.parse(raw);
          const locale = pickLocale(value);
          return locale || null;
        } catch (e) {
          return null;
        }
      })
      .catch(function () {
        return null;
      });
  };
};

/**
 * Get translations for locale
 * Returns a Map-like object that PureScript can use
 */
exports.getTranslations = function (locale) {
  return function () {
    const translations = loadTranslations(locale);
    const result = {};
    for (const key in translations) {
      if (translations.hasOwnProperty(key)) {
        result[key] = translations[key];
      }
    }
    return result;
  };
};

/**
 * Load translations for locale
 * This would load from actual translation files in production
 */
function loadTranslations(locale) {
  const baseTranslations = {
    "desktop.menu.checkForUpdates": "Check for Updates...",
    "desktop.menu.installCli": "Install CLI...",
    "desktop.menu.reloadWebview": "Reload Webview",
    "desktop.menu.restart": "Restart",
    "desktop.dialog.chooseFolder": "Choose a folder",
    "desktop.dialog.chooseFile": "Choose a file",
    "desktop.dialog.saveFile": "Save file",
    "desktop.updater.checkFailed.title": "Update Check Failed",
    "desktop.updater.checkFailed.message": "Failed to check for updates",
    "desktop.updater.none.title": "No Update Available",
    "desktop.updater.none.message": "You are already using the latest version of OpenCode",
    "desktop.updater.downloadFailed.title": "Update Failed",
    "desktop.updater.downloadFailed.message": "Failed to download update",
    "desktop.updater.downloaded.title": "Update Downloaded",
    "desktop.updater.downloaded.prompt": "Version {{version}} of OpenCode has been downloaded, would you like to install it and relaunch?",
    "desktop.updater.installFailed.title": "Update Failed",
    "desktop.updater.installFailed.message": "Failed to install update",
    "desktop.cli.installed.title": "CLI Installed",
    "desktop.cli.installed.message": "CLI installed to {{path}}\n\nRestart your terminal to use the 'opencode' command.",
    "desktop.cli.failed.title": "Installation Failed",
    "desktop.cli.failed.message": "Failed to install CLI: {{error}}",
    "desktop.error.serverStartFailed.title": "OpenCode failed to start",
    "desktop.error.serverStartFailed.description": "The local OpenCode server could not be started. Restart the app, or check your network settings (VPN/proxy) and try again."
  };
  
  if (locale === "en") {
    return baseTranslations;
  }
  
  const localeTranslations = getLocaleTranslations(locale);
  return Object.assign({}, baseTranslations, localeTranslations);
}

/**
 * Get locale-specific translations
 */
function getLocaleTranslations(locale) {
  const translations = {
    "zh": {
      "desktop.menu.checkForUpdates": "检查更新...",
      "desktop.menu.installCli": "安装 CLI...",
      "desktop.menu.reloadWebview": "重新加载 Webview",
      "desktop.menu.restart": "重启",
      "desktop.dialog.chooseFolder": "选择文件夹",
      "desktop.dialog.chooseFile": "选择文件",
      "desktop.dialog.saveFile": "保存文件",
      "desktop.updater.checkFailed.title": "检查更新失败",
      "desktop.updater.checkFailed.message": "无法检查更新",
      "desktop.updater.none.title": "没有可用更新",
      "desktop.updater.none.message": "你已经在使用最新版本的 OpenCode",
      "desktop.updater.downloadFailed.title": "更新失败",
      "desktop.updater.downloadFailed.message": "无法下载更新",
      "desktop.updater.downloaded.title": "更新已下载",
      "desktop.updater.downloaded.prompt": "已下载 OpenCode {{version}} 版本，是否安装并重启？",
      "desktop.updater.installFailed.title": "更新失败",
      "desktop.updater.installFailed.message": "无法安装更新",
      "desktop.cli.installed.title": "CLI 已安装",
      "desktop.cli.installed.message": "CLI 已安装到 {{path}}\n\n重启终端以使用 'opencode' 命令。",
      "desktop.cli.failed.title": "安装失败",
      "desktop.cli.failed.message": "无法安装 CLI: {{error}}",
      "desktop.error.serverStartFailed.title": "OpenCode 启动失败",
      "desktop.error.serverStartFailed.description": "无法启动本地 OpenCode 服务器。请重启应用，或检查网络设置 (VPN/proxy) 后重试。"
    }
  };
  
  return translations[locale] || {};
}
