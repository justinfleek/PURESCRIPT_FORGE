// Express.js FFI
"use strict";

var express = require("express");
var http = require("http");
var path = require("path");

exports.createApp = function() {
  return function() {
    return express();
  };
};

exports.createServer = function(app) {
  return function() {
    return http.createServer(app);
  };
};

exports.listen = function(server) {
  return function(port) {
    return function(host) {
      return function(callback) {
        server.listen(port, host, function() {
          callback();
        });
      };
    };
  };
};

exports.get = function(app) {
  return function(route) {
    return function(handler) {
      return function() {
        app.get(route, function(req, res) {
          handler(req)(res)();
        });
      };
    };
  };
};

exports.post = function(app) {
  return function(route) {
    return function(handler) {
      return function() {
        app.post(route, express.json(), function(req, res) {
          handler(req)(res)();
        });
      };
    };
  };
};

exports.useStatic = function(app) {
  return function(dir) {
    return function() {
      app.use(express.static(dir));
    };
  };
};

exports.sendJson = function(res) {
  return function(jsonStr) {
    return function() {
      res.json(JSON.parse(jsonStr));
    };
  };
};

exports.sendFile = function(res) {
  return function(dir) {
    return function(filename) {
      return function() {
        res.sendFile(path.join(dir, filename));
      };
    };
  };
};

exports.status = function(res) {
  return function(code) {
    return function() {
      res.status(code);
    };
  };
};
