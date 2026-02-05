"use strict";

const https = require("https");
const http = require("http");
const { URL } = require("url");

/**
 * HTTP POST with timeout
 */
exports.httpPostWithTimeout = function (timeout) {
  return function (url) {
    return function (body) {
      return function () {
        return new Promise(function (resolve, reject) {
          try {
            const parsedUrl = new URL(url);
            const isHttps = parsedUrl.protocol === "https:";
            const client = isHttps ? https : http;
            
            const options = {
              hostname: parsedUrl.hostname,
              port: parsedUrl.port || (isHttps ? 443 : 80),
              path: parsedUrl.pathname + parsedUrl.search,
              method: "POST",
              headers: {
                "Content-Type": "application/json",
                "Content-Length": Buffer.byteLength(body),
              },
              timeout: timeout,
            };
            
            const req = client.request(options, function (res) {
              let data = "";
              
              res.on("data", function (chunk) {
                data += chunk;
              });
              
              res.on("end", function () {
                resolve({
                  tag: "Right",
                  value: {
                    statusCode: res.statusCode,
                    body: data,
                  },
                });
              });
            });
            
            req.on("error", function (error) {
              resolve({
                tag: "Left",
                value: error.message || "HTTP request failed",
              });
            });
            
            req.on("timeout", function () {
              req.destroy();
              resolve({
                tag: "Left",
                value: "Request timeout",
              });
            });
            
            req.write(body);
            req.end();
          } catch (error) {
            resolve({
              tag: "Left",
              value: error.message || "Failed to make HTTP request",
            });
          }
        });
      };
    };
  };
};
