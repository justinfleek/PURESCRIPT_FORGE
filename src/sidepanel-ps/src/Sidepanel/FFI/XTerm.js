// xterm.js FFI implementation
"use strict";

var xterm = require("xterm");
var xtermFit = require("xterm-addon-fit");
var xtermWebLinks = require("xterm-addon-web-links");

exports.create = function(options) {
  return function() {
    var term = new xterm.Terminal({
      rows: options.rows || 24,
      cols: options.cols || 80,
      cursorBlink: options.cursorBlink !== undefined ? options.cursorBlink : true,
      fontSize: options.fontSize || 14,
      fontFamily: options.fontFamily || "monospace",
      theme: options.theme || {
        background: "#000000",
        foreground: "#ffffff",
        cursor: "#ffffff",
        selection: "#ffffff"
      }
    });
    
    // Add fit addon
    var fitAddon = new xtermFit.FitAddon();
    term.loadAddon(fitAddon);
    
    // Add web links addon
    var webLinksAddon = new xtermWebLinks.WebLinksAddon();
    term.loadAddon(webLinksAddon);
    
    // Store addons on terminal object
    term._fitAddon = fitAddon;
    
    return term;
  };
};

exports.open = function(term) {
  return function(elementId) {
    return function() {
      var element = document.getElementById(elementId);
      if (element) {
        term.open(element);
        // Fit terminal to container
        if (term._fitAddon) {
          term._fitAddon.fit();
        }
      }
    };
  };
};

exports.write = function(term) {
  return function(text) {
    return function() {
      term.write(text);
    };
  };
};

exports.writeln = function(term) {
  return function(text) {
    return function() {
      term.writeln(text);
    };
  };
};

exports.clear = function(term) {
  return function() {
    term.clear();
  };
};

exports.reset = function(term) {
  return function() {
    term.reset();
  };
};

exports.onData = function(term) {
  return function(handler) {
    return function() {
      term.onData(function(data) {
        handler(data)();
      });
    };
  };
};

exports.onLineFeed = function(term) {
  return function(handler) {
    return function() {
      term.onLineFeed(function() {
        handler();
      });
    };
  };
};

exports.resize = function(term) {
  return function(cols) {
    return function(rows) {
      return function() {
        term.resize(cols, rows);
      };
    };
  };
};

exports.focus = function(term) {
  return function() {
    term.focus();
  };
};

exports.blur = function(term) {
  return function() {
    term.blur();
  };
};

exports.dispose = function(term) {
  return function() {
    term.dispose();
  };
};

exports.elementId = function(term) {
  return function() {
    return term.element ? term.element.id : "";
  };
};
