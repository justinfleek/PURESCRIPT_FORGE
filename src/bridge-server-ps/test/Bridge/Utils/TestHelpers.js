// Test Helpers FFI Implementation
"use strict";

exports.getState = function(store) {
  return function() {
    return store.state.value;
  };
};

exports.getInitialState = function() {
  return function() {
    return {
      connected: false,
      balance: {
        venice: {
          diem: 0.0,
          usd: 0.0,
          effective: 0.0,
          lastUpdated: null
        },
        consumptionRate: 0.0,
        timeToDepletion: null,
        todayUsed: 0.0,
        todayStartBalance: 0.0,
        resetCountdown: null,
        alertLevel: "Normal"
      },
      session: null,
      proof: {
        connected: false,
        file: null,
        position: null,
        goals: [],
        diagnostics: [],
        suggestedTactics: []
      },
      metrics: {
        totalTokens: 0,
        totalCost: 0.0,
        averageResponseTime: 0.0,
        toolTimings: []
      }
    };
  };
};

exports.modify_ = function(f) {
  return function(ref) {
    return function() {
      var current = ref.value;
      ref.value = f(current);
    };
  };
};

exports.fromInt = function(n) {
  return n;
};

exports.getCurrentTimeMs = function() {
  return function() {
    return performance.now ? performance.now() : Date.now();
  };
};

exports.generateTestData = function(size) {
  var data = { test: "data", array: [] };
  var itemSize = Math.max(1, Math.floor(size / 100));
  for (var i = 0; i < 100; i++) {
    data.array.push({ id: i, content: "x".repeat(itemSize) });
  }
  return JSON.stringify(data);
};

exports.unsafeCoerce = function(x) {
  return x;
};
