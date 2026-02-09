// FFI bindings for Forge.Provider.Models PureScript module

// List custom models from FORGE_CUSTOM_MODELS env var
// Format: JSON array of {id, name, provider, contextLength} objects
export const listCustomModelsFFI = () => {
  return new Promise((resolve) => {
    var modelsJson = process.env.FORGE_CUSTOM_MODELS || "";
    if (!modelsJson) {
      resolve({ tag: "Right", value: [] });
      return;
    }
    try {
      var models = JSON.parse(modelsJson);
      if (!Array.isArray(models)) {
        resolve({ tag: "Left", value: "FORGE_CUSTOM_MODELS must be a JSON array" });
        return;
      }
      resolve({ tag: "Right", value: models });
    } catch (e) {
      resolve({ tag: "Left", value: "Failed to parse FORGE_CUSTOM_MODELS: " + e.message });
    }
  });
};

// Check if an API key is configured
export const checkApiKeyFFI = (envVar) => () => {
  return new Promise((resolve) => {
    if (!envVar || envVar === "") {
      resolve(true); // No API key required
      return;
    }
    
    // Check if environment variable is set
    const value = process.env[envVar];
    resolve(value !== undefined && value !== "");
  });
};
