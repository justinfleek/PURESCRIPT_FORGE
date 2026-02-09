// FFI for Forge.Provider.Provider
// 1:1 parity with opencode-dev/packages/opencode/src/provider/provider.ts

import { Log } from "../util/Log.js";
import { Config } from "../config/Config.js";

const log = Log.create({ service: "provider" });

// Model state cache
let providerState = null;

// Initialize providers from config and environment
async function initState() {
  if (providerState) return providerState;

  const config = await Config.get();
  const providers = {};

  // Load from environment variables
  const envProviders = [
    { id: "anthropic", env: "ANTHROPIC_API_KEY", npm: "@ai-sdk/anthropic" },
    { id: "openai", env: "OPENAI_API_KEY", npm: "@ai-sdk/openai" },
    { id: "google", env: "GOOGLE_API_KEY", npm: "@ai-sdk/google" },
    { id: "groq", env: "GROQ_API_KEY", npm: "@ai-sdk/groq" },
    { id: "mistral", env: "MISTRAL_API_KEY", npm: "@ai-sdk/mistral" },
    { id: "xai", env: "XAI_API_KEY", npm: "@ai-sdk/xai" },
    { id: "openrouter", env: "OPENROUTER_API_KEY", npm: "@openrouter/ai-sdk-provider" },
    { id: "deepinfra", env: "DEEPINFRA_API_KEY", npm: "@ai-sdk/deepinfra" },
    { id: "cerebras", env: "CEREBRAS_API_KEY", npm: "@ai-sdk/cerebras" },
    { id: "perplexity", env: "PERPLEXITY_API_KEY", npm: "@ai-sdk/perplexity" },
    { id: "together", env: "TOGETHER_API_KEY", npm: "@ai-sdk/togetherai" },
    { id: "cohere", env: "COHERE_API_KEY", npm: "@ai-sdk/cohere" },
  ];

  for (const { id, env, npm } of envProviders) {
    const apiKey = process.env[env];
    if (apiKey) {
      providers[id] = {
        id,
        name: id.charAt(0).toUpperCase() + id.slice(1),
        source: "env",
        env: [env],
        key: apiKey,
        options: {},
        models: {},
      };
      log.info("provider loaded from env", { id });
    }
  }

  // Merge with config providers
  const configProviders = config?.provider || {};
  for (const [id, provider] of Object.entries(configProviders)) {
    if (providers[id]) {
      providers[id] = { ...providers[id], ...provider, source: "config" };
    } else {
      providers[id] = {
        id,
        name: provider.name || id,
        source: "config",
        env: provider.env || [],
        options: provider.options || {},
        models: provider.models || {},
      };
    }
    log.info("provider loaded from config", { id });
  }

  providerState = { providers };
  return providerState;
}

// List all providers
export async function list() {
  const state = await initState();
  return state.providers;
}

// Get a specific provider
export async function getProvider(providerID) {
  const state = await initState();
  return state.providers[providerID];
}

// Get a specific model
export async function getModel(providerID, modelID) {
  const state = await initState();
  const provider = state.providers[providerID];
  if (!provider) {
    throw new ModelNotFoundError(providerID, modelID, Object.keys(state.providers).slice(0, 3));
  }
  const model = provider.models?.[modelID];
  if (!model) {
    throw new ModelNotFoundError(providerID, modelID, Object.keys(provider.models || {}).slice(0, 3));
  }
  return model;
}

// Get default model based on config
export async function defaultModel() {
  const config = await Config.get();
  if (config?.model) {
    return parseModel(config.model);
  }

  const providers = await list();
  const providerIds = Object.keys(providers);
  if (providerIds.length === 0) {
    throw new Error("No providers configured");
  }

  // Return first available provider/model
  const provider = providers[providerIds[0]];
  const modelIds = Object.keys(provider.models || {});
  if (modelIds.length === 0) {
    throw new Error("No models available");
  }

  return {
    providerID: provider.id,
    modelID: modelIds[0],
  };
}

// Parse "provider/model" string
export function parseModel(modelString) {
  const [providerID, ...rest] = modelString.split("/");
  return {
    providerID,
    modelID: rest.join("/"),
  };
}

// Error class for model not found
export class ModelNotFoundError extends Error {
  constructor(providerID, modelID, suggestions = []) {
    super(`Model not found: ${providerID}/${modelID}`);
    this.name = "ModelNotFoundError";
    this.providerID = providerID;
    this.modelID = modelID;
    this.suggestions = suggestions;
  }
}

// Provider namespace
export const Provider = {
  list,
  getProvider,
  getModel,
  defaultModel,
  parseModel,
  ModelNotFoundError,
};

// PureScript FFI exports
export const listFFI = async () => {
  try {
    const providers = await list();
    return { tag: "Right", value: Object.values(providers) };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const getProviderFFI = (providerID) => async () => {
  try {
    const provider = await getProvider(providerID);
    if (!provider) {
      return { tag: "Right", value: null };
    }
    return { tag: "Right", value: provider };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const getModelFFI = (providerID) => (modelID) => async () => {
  try {
    const model = await getModel(providerID, modelID);
    return { tag: "Right", value: model };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const defaultModelFFI = async () => {
  try {
    const model = await defaultModel();
    return { tag: "Right", value: model };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

export const parseModelFFI = (modelString) => parseModel(modelString);
