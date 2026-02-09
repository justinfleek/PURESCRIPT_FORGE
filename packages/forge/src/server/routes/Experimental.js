// FFI for Forge.Server.Routes.Experimental
// 1:1 parity with opencode-dev/packages/opencode/src/server/routes/experimental.ts

import { Log } from "../../util/Log.js";

const log = Log.create({ service: "experimental" });

// Experimental features registry
const features = new Map([
  ["batch_tool", { enabled: false, description: "Batch tool execution" }],
  ["lsp_tool", { enabled: false, description: "LSP integration tool" }],
  ["plan_mode", { enabled: false, description: "Plan mode for complex tasks" }],
  ["auto_share", { enabled: false, description: "Automatic session sharing" }],
]);

// Execute experimental endpoint
export const experimentalFFI = (endpoint) => async () => {
  try {
    log.info("experimental endpoint", { endpoint });
    
    switch (endpoint) {
      case "features":
        return {
          tag: "Right",
          value: Object.fromEntries(features),
        };
        
      case "enable":
        // Would need additional params in full implementation
        return { tag: "Right", value: { enabled: true } };
        
      case "disable":
        return { tag: "Right", value: { enabled: false } };
        
      default:
        return { tag: "Left", value: `Unknown experimental endpoint: ${endpoint}` };
    }
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// List experimental features
export const listFeaturesFFI = async () => {
  try {
    return {
      tag: "Right",
      value: Array.from(features.entries()).map(([id, info]) => ({
        id,
        ...info,
      })),
    };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Enable experimental feature
export const enableFeatureFFI = (featureID) => async () => {
  try {
    const feature = features.get(featureID);
    if (!feature) {
      return { tag: "Left", value: `Unknown feature: ${featureID}` };
    }
    feature.enabled = true;
    log.info("experimental feature enabled", { featureID });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Disable experimental feature
export const disableFeatureFFI = (featureID) => async () => {
  try {
    const feature = features.get(featureID);
    if (!feature) {
      return { tag: "Left", value: `Unknown feature: ${featureID}` };
    }
    feature.enabled = false;
    log.info("experimental feature disabled", { featureID });
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
