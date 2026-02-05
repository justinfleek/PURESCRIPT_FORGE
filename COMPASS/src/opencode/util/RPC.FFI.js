"use strict";

/**
 * RPC FFI
 * Provides RPC call utilities
 */

const http = require("http");
const https = require("https");
const { URL } = require("url");

// | Call an RPC method
exports.callRPC = function (endpoint) {
  return function (request) {
    return function () {
      return new Promise(function (resolve) {
        try {
          const url = new URL(endpoint);
          const isHttps = url.protocol === "https:";
          const client = isHttps ? https : http;
          
          const rpcRequest = {
            jsonrpc: "2.0",
            method: request.method,
            params: JSON.parse(request.params),
            id: request.id
          };
          
          const options = {
            hostname: url.hostname,
            port: url.port || (isHttps ? 443 : 80),
            path: url.pathname,
            method: "POST",
            headers: {
              "Content-Type": "application/json",
              "Content-Length": JSON.stringify(rpcRequest).length
            }
          };
          
          const req = client.request(options, function (res) {
            let data = "";
            
            res.on("data", function (chunk) {
              data += chunk;
            });
            
            res.on("end", function () {
              try {
                const response = JSON.parse(data);
                resolve({
                  tag: "Right",
                  value: {
                    result: JSON.stringify(response.result || ""),
                    error: response.error ? JSON.stringify(response.error) : "",
                    id: response.id || request.id
                  }
                });
              } catch (error) {
                resolve({
                  tag: "Left",
                  value: "Failed to parse RPC response: " + error.message
                });
              }
            });
          });
          
          req.on("error", function (error) {
            resolve({
              tag: "Left",
              value: "RPC request failed: " + error.message
            });
          });
          
          req.write(JSON.stringify(rpcRequest));
          req.end();
        } catch (error) {
          resolve({
            tag: "Left",
            value: "Invalid endpoint or request: " + error.message
          });
        }
      });
    };
  };
};
