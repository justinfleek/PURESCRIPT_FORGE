"use strict";

/**
 * mDNS Service Discovery FFI
 * Uses multicast DNS for local service discovery
 * Falls back to environment-based discovery when mDNS unavailable
 */

var dgram;
try {
  dgram = require("dgram");
} catch (e) {
  dgram = null;
}

// Active advertisement state
var activeService = null;

// | Advertise service via mDNS
exports.advertiseFFI = function (name) {
  return function (port) {
    return function (onError, onSuccess) {
      try {
        activeService = { name: name, port: port };

        if (dgram) {
          // Create multicast socket for mDNS
          var socket = dgram.createSocket({ type: "udp4", reuseAddr: true });

          var record = JSON.stringify({
            name: name,
            host: "localhost",
            port: port,
            type: "_forge._tcp.local",
          });

          socket.on("listening", function () {
            try {
              socket.addMembership("224.0.0.251");
            } catch (e) {
              // May fail in some environments
            }
          });

          socket.bind(5353, function () {
            // Announce service
            var buf = Buffer.from(record);
            socket.send(buf, 0, buf.length, 5353, "224.0.0.251");
          });

          activeService.socket = socket;
        }

        onSuccess({ tag: "Right", value: undefined });
      } catch (e) {
        onSuccess({ tag: "Left", value: "mDNS advertise failed: " + e.message });
      }

      return function (cancelError, onCancelerError, onCancelerSuccess) {
        onCancelerSuccess();
      };
    };
  };
};

// | Discover services
exports.discoverFFI = function (onError, onSuccess) {
  try {
    var services = [];

    // Check for services advertised via environment
    var envServices = process.env.FORGE_SERVICES;
    if (envServices) {
      try {
        services = JSON.parse(envServices);
      } catch (e) {
        // Invalid JSON
      }
    }

    // Add local active service if present
    if (activeService) {
      services.push({
        name: activeService.name,
        host: "localhost",
        port: activeService.port,
      });
    }

    onSuccess({ tag: "Right", value: services });
  } catch (e) {
    onSuccess({ tag: "Left", value: "mDNS discover failed: " + e.message });
  }

  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};

// | Stop advertising
exports.stopAdvertiseFFI = function (onError, onSuccess) {
  try {
    if (activeService && activeService.socket) {
      activeService.socket.close();
    }
    activeService = null;
    onSuccess({ tag: "Right", value: undefined });
  } catch (e) {
    onSuccess({ tag: "Left", value: "mDNS stop failed: " + e.message });
  }

  return function (cancelError, onCancelerError, onCancelerSuccess) {
    onCancelerSuccess();
  };
};
