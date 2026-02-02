// FFI for Opencode.Server.Event
// Provides global refs for event subscription system

"use strict";

// Global subscribers array ref
let subscribers = [];
export const subscribersRef = {
  value: subscribers,
  read: () => subscribers,
  write: (v) => { subscribers = v; },
  modify_: (f) => { subscribers = f(subscribers); }
};

// Counter for subscription IDs
let counter = 0;
export const counterRef = {
  value: counter,
  read: () => counter,
  write: (v) => { counter = v; }
};
