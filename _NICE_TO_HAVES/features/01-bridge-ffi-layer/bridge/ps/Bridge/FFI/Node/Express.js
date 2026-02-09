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

exports.useStatic = function(app) {
  return function(dir) {
    return function() {
      app.use(express.static(dir));
    };
  };
};

exports.sendJson = function(res) {
  return function(json) {
    return function() {
      res.json(JSON.parse(json));
    };
  };
};

exports.sendFile = function(res) {
  return function(root) {
    return function(file) {
      return function() {
        res.sendFile(file, { root: root });
      };
    };
  };
};

exports.getPath = function(req) {
  return function() {
    return req.path;
  };
};

exports.getMethod = function(req) {
  return function() {
    return req.method;
  };
};
