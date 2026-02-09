// FFI for Forge.Server.Routes.Provider
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/provider.ts

import { Provider } from "../../provider/Provider.js";

// List all providers
export const listFFI = async () => {
  try {
    const providers = await Provider.list();
    return { tag: "Right", value: Object.values(providers) };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get a specific provider
export const getFFI = (providerID) => async () => {
  try {
    const provider = await Provider.getProvider(providerID);
    if (!provider) {
      return { tag: "Right", value: null };
    }
    return { tag: "Right", value: provider };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Get available models for a provider
export const modelsFFI = (providerID) => async () => {
  try {
    const provider = await Provider.getProvider(providerID);
    if (!provider) {
      return { tag: "Left", value: "Provider not found" };
    }
    return { tag: "Right", value: Object.values(provider.models || {}) };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
