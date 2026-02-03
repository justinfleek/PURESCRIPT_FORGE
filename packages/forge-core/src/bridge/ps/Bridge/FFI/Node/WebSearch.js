// Web Search FFI Implementation
"use strict";

// Helper: Explicit default value (replaces banned || pattern)
function explicitDefault(value, defaultValue) {
  if (value === undefined || value === null) {
    return defaultValue;
  }
  return value;
}

const https = require('https');
const http = require('http');

// | Execute web search
// | Uses Forge SDK web_search tool if available, otherwise falls back to DuckDuckGo API
exports.searchWeb = function(request) {
  return function() {
    return new Promise(function(resolve) {
      try {
      // For now, use DuckDuckGo Instant Answer API as fallback
      // In production, this should integrate with Forge SDK's web_search tool
      const query = encodeURIComponent(request.query);
      const maxResults = explicitDefault(request.maxResults, 10);
      
      // DuckDuckGo Instant Answer API (no API key required)
      const url = `https://api.duckduckgo.com/?q=${query}&format=json&no_html=1&skip_disambig=1`;
      
        https.get(url, function(res) {
          let data = '';
          
          res.on('data', function(chunk) {
            data += chunk;
          });
          
          res.on('end', function() {
            try {
              const ddgResult = JSON.parse(data);
              
              // Transform DuckDuckGo results to our format
              const results = [];
              
              // Add abstract if available
              if (ddgResult.Abstract && ddgResult.AbstractText) {
                results.push({
                  title: ddgResult.Heading !== undefined && ddgResult.Heading !== null ? ddgResult.Heading : explicitDefault(ddgResult.AbstractSource, ""),
                  url: explicitDefault(ddgResult.AbstractURL, ""),
                  snippet: ddgResult.AbstractText,
                  relevance: 1.0
                });
              }
              
              // Add related topics
              if (ddgResult.RelatedTopics && Array.isArray(ddgResult.RelatedTopics)) {
                ddgResult.RelatedTopics.slice(0, maxResults - results.length).forEach(function(topic) {
                  if (topic.Text && topic.FirstURL) {
                    results.push({
                      title: (function() {
                        var splitResult = topic.Text.split(' - ');
                        return splitResult.length > 0 && splitResult[0] !== undefined && splitResult[0] !== null && splitResult[0] !== "" ? splitResult[0] : topic.Text;
                      })(),
                      url: topic.FirstURL,
                      snippet: topic.Text,
                      relevance: 0.8
                    });
                  }
                });
              }
              
              // Add results if available
              if (ddgResult.Results && Array.isArray(ddgResult.Results)) {
                ddgResult.Results.slice(0, maxResults - results.length).forEach(function(result) {
                  results.push({
                    title: result.Text !== undefined && result.Text !== null ? result.Text : explicitDefault(result.FirstURL, ""),
                    url: explicitDefault(result.FirstURL, ""),
                    snippet: explicitDefault(result.Text, ""),
                    relevance: 0.7
                  });
                });
              }
              
              // If no results, try web search via DuckDuckGo HTML (fallback)
              if (results.length === 0) {
                // For now, return empty results
                // In production, could scrape DuckDuckGo HTML results or use another API
                resolve({
                  tag: "Right",
                  value: {
                    success: true,
                    results: [],
                    query: request.query,
                    totalResults: 0
                  }
                });
              } else {
                resolve({
                  tag: "Right",
                  value: {
                    success: true,
                    results: results.slice(0, maxResults),
                    query: request.query,
                    totalResults: results.length
                  }
                });
              }
            } catch (e) {
              resolve({
                tag: "Left",
                value: "Failed to parse search results: " + e.message
              });
            }
          });
        }).on('error', function(err) {
          resolve({
            tag: "Left",
            value: "Search request failed: " + err.message
          });
        });
      } catch (e) {
        resolve({
          tag: "Left",
          value: "Search error: " + e.message
        });
      }
    });
  };
};
