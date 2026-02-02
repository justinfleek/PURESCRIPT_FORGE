// | FFI JavaScript bindings for Edge Routing
// | Region detection and agent routing to closest Fly.io region

const { spawn } = require('child_process');
const path = require('path');

// | Detect user location from HTTP headers
exports.detectUserLocationFromHeaders = function() {
  // In production, would parse headers from request context
  // For now, check environment variables and headers
  const cfCountry = process.env.CF_IPCOUNTRY;
  const flyRegion = process.env.FLY_REGION;
  
  if (flyRegion) {
    // Use Fly.io region header
    return {
      lat: null,
      lon: null,
      country: null,
      city: null,
      ipAddress: null
    };
  }
  
  if (cfCountry) {
    // Use Cloudflare country header
    return {
      lat: null,
      lon: null,
      country: cfCountry,
      city: null,
      ipAddress: null
    };
  }
  
  return null;
};

// | Find closest Fly.io region to user location
exports.findClosestRegion_ = function(userLoc) {
  const regions = [
    { code: "ord", city: "Chicago", country: "United States", lat: 41.8781, lon: -87.6298 },
    { code: "sjc", city: "San Jose", country: "United States", lat: 37.3382, lon: -121.8863 },
    { code: "lhr", city: "London", country: "United Kingdom", lat: 51.5074, lon: -0.1278 },
    { code: "nrt", city: "Tokyo", country: "Japan", lat: 35.6762, lon: 139.6503 },
    { code: "iad", city: "Washington DC", country: "United States", lat: 38.9072, lon: -77.0369 },
    { code: "fra", city: "Frankfurt", country: "Germany", lat: 50.1109, lon: 8.6821 },
    { code: "sin", city: "Singapore", country: "Singapore", lat: 1.3521, lon: 103.8198 },
    { code: "syd", city: "Sydney", country: "Australia", lat: -33.8688, lon: 151.2093 },
    { code: "gru", city: "São Paulo", country: "Brazil", lat: -23.5505, lon: -46.6333 },
    { code: "yyz", city: "Toronto", country: "Canada", lat: 43.6532, lon: -79.3832 }
  ];
  
  // If user has explicit coordinates, calculate distance
  if (userLoc.lat !== null && userLoc.lon !== null) {
    let closestRegion = regions[0];
    let minDistance = Infinity;
    
    for (const region of regions) {
      const distance = haversineDistance(
        userLoc.lat,
        userLoc.lon,
        region.lat,
        region.lon
      );
      
      if (distance < minDistance) {
        minDistance = distance;
        closestRegion = region;
      }
    }
    
    return closestRegion;
  }
  
  // If user has country, use country-based default
  if (userLoc.country) {
    const countryDefaults = {
      "US": regions.find(r => r.code === "ord"),
      "GB": regions.find(r => r.code === "lhr"),
      "JP": regions.find(r => r.code === "nrt"),
      "DE": regions.find(r => r.code === "fra"),
      "SG": regions.find(r => r.code === "sin"),
      "AU": regions.find(r => r.code === "syd"),
      "BR": regions.find(r => r.code === "gru"),
      "CA": regions.find(r => r.code === "yyz")
    };
    
    const defaultRegion = countryDefaults[userLoc.country];
    if (defaultRegion) {
      return defaultRegion;
    }
  }
  
  // Default to ORD (Chicago)
  return regions.find(r => r.code === "ord");
};

// | Haversine distance formula (in kilometers)
function haversineDistance(lat1, lon1, lat2, lon2) {
  const R = 6371.0;  // Earth radius in kilometers
  const dLat = degToRad(lat2 - lat1);
  const dLon = degToRad(lon2 - lon1);
  const a = Math.sin(dLat / 2) * Math.sin(dLat / 2) +
            Math.cos(degToRad(lat1)) * Math.cos(degToRad(lat2)) *
            Math.sin(dLon / 2) * Math.sin(dLon / 2);
  const c = 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1 - a));
  return R * c;
}

function degToRad(deg) {
  return deg * Math.PI / 180.0;
}

// | Call agent in specific region
exports.callAgentInRegion_ = function(regionCode, request) {
  return new Promise((resolve, reject) => {
    // In production, would make HTTP request to agent endpoint in that region
    // For now, call Haskell CLI executable
    const args = [
      "call-agent",
      "--region", regionCode,
      "--method", request.method,
      "--params", JSON.stringify(request.params)
    ];
    
    const proc = spawn('nexus-edge-orchestrator-cli', args, {
      env: { ...process.env },
      stdio: ['pipe', 'pipe', 'pipe']
    });
    
    let stdout = '';
    let stderr = '';
    
    proc.stdout.on('data', (data) => {
      stdout += data.toString();
    });
    
    proc.stderr.on('data', (data) => {
      stderr += data.toString();
    });
    
    proc.on('close', (code) => {
      if (code !== 0) {
        reject(new Error(`Agent call failed: ${stderr}`));
      } else {
        try {
          const response = JSON.parse(stdout);
          resolve({
            success: true,
            data: response,
            region: regionCode,
            latencyMs: 0  // Would measure actual latency
          });
        } catch (err) {
          reject(new Error(`Failed to parse response: ${err.message}`));
        }
      }
    });
    
    proc.on('error', (err) => {
      reject(err);
    });
  });
};

// | Launch agent in specific region
exports.launchAgentInRegion_ = function(regionCode, agentType, config) {
  return new Promise((resolve, reject) => {
    // Call Haskell CLI executable
    const args = [
      "launch",
      "--agent-type", agentType,
      "--region", regionCode,
      "--config", config
    ];
    
    const proc = spawn('nexus-edge-orchestrator-cli', args, {
      env: { ...process.env },
      stdio: ['pipe', 'pipe', 'pipe']
    });
    
    let stdout = '';
    let stderr = '';
    
    proc.stdout.on('data', (data) => {
      stdout += data.toString();
    });
    
    proc.stderr.on('data', (data) => {
      stderr += data.toString();
    });
    
    proc.on('close', (code) => {
      if (code !== 0) {
        reject(new Error(`Agent launch failed: ${stderr}`));
      } else {
        try {
          const response = JSON.parse(stdout);
          resolve({
            success: true,
            agentId: response.agentId || response.machineId
          });
        } catch (err) {
          reject(new Error(`Failed to parse response: ${err.message}`));
        }
      }
    });
    
    proc.on('error', (err) => {
      reject(err);
    });
  });
};
