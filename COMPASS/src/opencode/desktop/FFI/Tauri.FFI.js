"use strict";

const { invoke } = require("@tauri-apps/api/core");
const { message, ask } = require("@tauri-apps/plugin-dialog");
const { type: ostype } = require("@tauri-apps/plugin-os");
const { relaunch } = require("@tauri-apps/plugin-process");
const { Menu, MenuItem, PredefinedMenuItem, Submenu } = require("@tauri-apps/api/menu");
const { check } = require("@tauri-apps/plugin-updater");

/**
 * Invoke Tauri command to install CLI
 */
exports.invokeInstallCLI = function () {
  return function () {
    return invoke("install_cli")
      .then(function (path) {
        return { tag: "Right", value: path };
      })
      .catch(function (error) {
        return { tag: "Left", value: String(error) };
      });
  };
};

/**
 * Show message dialog
 */
exports.showMessage = function (msg) {
  return function (options) {
    return function () {
      return message(msg, options);
    };
  };
};

/**
 * Show ask dialog
 */
exports.ask = function (prompt) {
  return function (options) {
    return function () {
      return ask(prompt, options);
    };
  };
};

/**
 * Get OS type
 */
exports.getOSType = function () {
  return ostype();
};

/**
 * Create menu
 */
exports.createMenu = function (items) {
  return function () {
    return Menu.new({ items: items });
  };
};

/**
 * Set as app menu
 */
exports.setAsAppMenu = function (menu) {
  return function () {
    return menu.setAsAppMenu();
  };
};

/**
 * Create submenu
 */
exports.createSubmenu = function (text) {
  return function (items) {
    return function () {
      return Submenu.new({ text: text, items: items });
    };
  };
};

/**
 * Create menu item
 */
exports.menuItem = function (text) {
  return function (action) {
    return MenuItem.new({
      text: text,
      action: function () {
        return action();
      },
    });
  };
};

/**
 * Create predefined menu item
 */
exports.predefinedMenuItem = function (itemType) {
  return PredefinedMenuItem.new({ item: itemType });
};

/**
 * Check for updates
 */
exports.checkForUpdates = function () {
  return function () {
    return check()
      .then(function (update) {
        return { tag: "Right", value: update || null };
      })
      .catch(function (error) {
        return { tag: "Left", value: String(error) };
      });
  };
};

/**
 * Get update version
 */
exports.getUpdateVersion = function (update) {
  return update.version;
};

/**
 * Download update
 */
exports.downloadUpdate = function (update) {
  return function () {
    return update.download()
      .then(function () {
        return { tag: "Right", value: null };
      })
      .catch(function (error) {
        return { tag: "Left", value: String(error) };
      });
  };
};

/**
 * Install update
 */
exports.installUpdate = function (update) {
  return function () {
    return update.install()
      .then(function () {
        return { tag: "Right", value: null };
      })
      .catch(function (error) {
        return { tag: "Left", value: String(error) };
      });
  };
};

/**
 * Reload webview
 */
exports.reloadWebview = function () {
  return function () {
    window.location.reload();
  };
};

/**
 * Relaunch application
 */
exports.relaunch = function () {
  return function () {
    return relaunch();
  };
};

/**
 * Kill sidecar process
 */
exports.killSidecar = function () {
  return function () {
    return invoke("kill_sidecar").catch(function () {
      return null;
    });
  };
};
