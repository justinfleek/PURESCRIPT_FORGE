"use strict";

const https = require("https");
const http = require("http");
const { URL } = require("url");

/**
 * Perform HTTP GET request
 */
exports.httpGet = function (url) {
  return function () {
    return new Promise((resolve, reject) => {
      const parsedUrl = new URL(url);
      const client = parsedUrl.protocol === "https:" ? https : http;
      
      const options = {
        hostname: parsedUrl.hostname,
        port: parsedUrl.port || (parsedUrl.protocol === "https:" ? 443 : 80),
        path: parsedUrl.pathname + parsedUrl.search,
        method: "GET",
        headers: {
          "Accept": "application/json",
          "User-Agent": "SearXNG-Client/1.0",
        },
      };
      
      const req = client.request(options, (res) => {
        let body = "";
        
        res.on("data", (chunk) => {
          body += chunk.toString();
        });
        
        res.on("end", () => {
          const headers = Object.entries(res.headers).map(([key, value]) => ({
            key,
            value: Array.isArray(value) ? value.join(", ") : String(value),
          }));
          
          resolve({
            tag: "Right",
            value: {
              statusCode: res.statusCode || 200,
              headers: headers,
              body: body,
            },
          });
        });
      });
      
      req.on("error", (err) => {
        resolve({
          tag: "Left",
          value: err.message,
        });
      });
      
      req.setTimeout(10000, () => {
        req.destroy();
        resolve({
          tag: "Left",
          value: "Request timeout",
        });
      });
      
      req.end();
    });
  };
};

/**
 * Perform HTTP GET request with custom timeout
 */
exports.httpGetWithTimeout = function (timeoutMs) {
  return function (url) {
    return function () {
      return new Promise((resolve, reject) => {
        const parsedUrl = new URL(url);
        const client = parsedUrl.protocol === "https:" ? https : http;
        
        const options = {
          hostname: parsedUrl.hostname,
          port: parsedUrl.port || (parsedUrl.protocol === "https:" ? 443 : 80),
          path: parsedUrl.pathname + parsedUrl.search,
          method: "GET",
          headers: {
            "Accept": "application/json",
            "User-Agent": "SearXNG-Client/1.0",
          },
        };
        
        const req = client.request(options, (res) => {
          let body = "";
          
          res.on("data", (chunk) => {
            body += chunk.toString();
          });
          
          res.on("end", () => {
            const headers = Object.entries(res.headers).map(([key, value]) => ({
              key,
              value: Array.isArray(value) ? value.join(", ") : String(value),
            }));
            
            resolve({
              tag: "Right",
              value: {
                statusCode: res.statusCode || 200,
                headers: headers,
                body: body,
              },
            });
          });
        });
        
        req.on("error", (err) => {
          resolve({
            tag: "Left",
            value: err.message,
          });
        });
        
        req.setTimeout(timeoutMs, () => {
          req.destroy();
          resolve({
            tag: "Left",
            value: "Request timeout",
          });
        });
        
        req.end();
      });
    };
  };
};

/**
 * Get current timestamp in milliseconds
 */
exports.nowMillis = function () {
  return Date.now();
};

/**
 * Hash a string (simple hash for proof - would use crypto in production)
 */
exports.hashString = function (str) {
  var hash = 0;
  for (var i = 0; i < str.length; i++) {
    var char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash; // Convert to 32bit integer
  }
  return Math.abs(hash).toString(36);
};
