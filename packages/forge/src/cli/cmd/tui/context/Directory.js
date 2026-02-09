"use strict";

/**
 * Directory context FFI
 * Provides working directory detection and navigation
 */

var child_process = require("child_process");
var path = require("path");
var fs = require("fs");

// | Find git root from a directory
function findGitRoot(dir) {
  try {
    var result = child_process.execSync("git rev-parse --show-toplevel", {
      cwd: dir,
      encoding: "utf-8",
      timeout: 5000,
      stdio: ["pipe", "pipe", "pipe"],
    });
    return result.trim();
  } catch (e) {
    return dir;
  }
}

// | Find project root (directory with package.json, spago.dhall, cabal file, etc.)
function findProjectRoot(dir) {
  var markers = [
    "package.json",
    "spago.dhall",
    "spago.yaml",
    "flake.nix",
    "lakefile.lean",
    "lakefile.toml",
    "Cargo.toml",
    "go.mod",
    "stack.yaml",
  ];

  var current = dir;
  while (current !== path.dirname(current)) {
    for (var i = 0; i < markers.length; i++) {
      if (fs.existsSync(path.join(current, markers[i]))) {
        return current;
      }
    }
    current = path.dirname(current);
  }

  return dir;
}

// | Get directory context
exports.getDirectoryContextFFI = function (onError, onSuccess) {
  try {
    var cwd = process.cwd();
    var gitRoot = findGitRoot(cwd);
    var projectRoot = findProjectRoot(cwd);

    onSuccess({
      tag: "Right",
      value: {
        cwd: cwd,
        projectRoot: projectRoot,
        gitRoot: gitRoot,
      },
    });
  } catch (e) {
    onSuccess({
      tag: "Left",
      value: "Failed to get directory context: " + e.message,
    });
  }

  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};

// | Change working directory
exports.changeDirectoryFFI = function (dir) {
  return function (onError, onSuccess) {
    try {
      var resolved = path.resolve(dir);

      if (!fs.existsSync(resolved)) {
        onSuccess({ tag: "Left", value: "Directory does not exist: " + resolved });
        return function (c, ce, cs) { cs(); };
      }

      var stat = fs.statSync(resolved);
      if (!stat.isDirectory()) {
        onSuccess({ tag: "Left", value: "Not a directory: " + resolved });
        return function (c, ce, cs) { cs(); };
      }

      process.chdir(resolved);
      onSuccess({ tag: "Right", value: undefined });
    } catch (e) {
      onSuccess({ tag: "Left", value: "Failed to change directory: " + e.message });
    }

    return function (cancelError, onCancelerError, onCancelerSuccess) {
      onCancelerSuccess();
    };
  };
};
