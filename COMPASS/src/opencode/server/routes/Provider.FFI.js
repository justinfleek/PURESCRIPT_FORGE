"use strict";

/**
 * Provider Routes FFI
 * Provides OAuth token exchange utilities
 */

const http = require("http");
const https = require("https");
const { URL } = require("url");

// | Exchange OAuth authorization code for access token
exports.exchangeOAuthCode = function (providerID) {
  return function (code) {
    return function () {
      return new Promise(function (resolve) {
        try {
          // Build token exchange URL based on provider
          const tokenUrl = getTokenUrl(providerID);
          const clientId = process.env[providerID.toUpperCase() + "_CLIENT_ID"] || "opencode";
          const clientSecret = process.env[providerID.toUpperCase() + "_CLIENT_SECRET"] || "";
          const redirectUri = "http://localhost:4096/provider/" + providerID + "/oauth/callback";
          
          const url = new URL(tokenUrl);
          const isHttps = url.protocol === "https:";
          const client = isHttps ? https : http;
          
          const postData = JSON.stringify({
            grant_type: "authorization_code",
            code: code,
            client_id: clientId,
            client_secret: clientSecret,
            redirect_uri: redirectUri
          });
          
          const options = {
            hostname: url.hostname,
            port: url.port || (isHttps ? 443 : 80),
            path: url.pathname,
            method: "POST",
            headers: {
              "Content-Type": "application/json",
              "Content-Length": Buffer.byteLength(postData)
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
                if (response.access_token) {
                  resolve({
                    tag: "Right",
                    value: {
                      accessToken: response.access_token,
                      refreshToken: response.refresh_token || null,
                      expiresIn: response.expires_in || null
                    }
                  });
                } else {
                  resolve({
                    tag: "Left",
                    value: "No access token in response"
                  });
                }
              } catch (error) {
                resolve({
                  tag: "Left",
                  value: "Failed to parse token response: " + error.message
                });
              }
            });
          });
          
          req.on("error", function (error) {
            resolve({
              tag: "Left",
              value: "Token exchange failed: " + error.message
            });
          });
          
          req.write(postData);
          req.end();
        } catch (error) {
          resolve({
            tag: "Left",
            value: "Token exchange error: " + error.message
          });
        }
      });
    };
  };
};

// | Get token exchange URL for provider
function getTokenUrl(providerID) {
  const urls = {
    "anthropic": "https://api.anthropic.com/oauth/token",
    "openai": "https://api.openai.com/v1/oauth/token",
    "google": "https://oauth2.googleapis.com/token",
    "github": "https://github.com/login/oauth/access_token"
  };
  return urls[providerID] || "https://auth." + providerID + ".com/oauth/token";
}

// | Store provider authentication
exports.storeProviderAuth = function (providerID) {
  return function (tokens) {
    return function () {
      return new Promise(function (resolve) {
        // In production, this would store in persistent storage
        // For now, resolve successfully (storage handled by Provider.Auth module)
        resolve({
          tag: "Right",
          value: null
        });
      });
    };
  };
};
