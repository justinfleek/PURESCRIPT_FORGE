// xterm.js FFI implementation
import * as xterm from "xterm";
import * as xtermFit from "xterm-addon-fit";
import * as xtermWebLinks from "xterm-addon-web-links";

export const create = function(options) {
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

export const open = function(term) {
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

export const write = function(term) {
  return function(text) {
    return function() {
      term.write(text);
    };
  };
};

export const writeln = function(term) {
  return function(text) {
    return function() {
      term.writeln(text);
    };
  };
};

export const clear = function(term) {
  return function() {
    term.clear();
  };
};

export const reset = function(term) {
  return function() {
    term.reset();
  };
};

export const onData = function(term) {
  return function(handler) {
    return function() {
      term.onData(function(data) {
        handler(data)();
      });
    };
  };
};

export const onLineFeed = function(term) {
  return function(handler) {
    return function() {
      term.onLineFeed(function() {
        handler();
      });
    };
  };
};

export const resize = function(term) {
  return function(cols) {
    return function(rows) {
      return function() {
        term.resize(cols, rows);
      };
    };
  };
};

export const focus = function(term) {
  return function() {
    term.focus();
  };
};

export const blur = function(term) {
  return function() {
    term.blur();
  };
};

export const dispose = function(term) {
  return function() {
    term.dispose();
  };
};

export const elementId = function(term) {
  return function() {
    return term.element ? term.element.id : "";
  };
};
