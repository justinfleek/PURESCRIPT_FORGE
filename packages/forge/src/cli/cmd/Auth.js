// FFI for Forge.CLI.Cmd.Auth
// 1:1 parity with opencode-dev/packages/opencode/src/cli/cmd/auth.ts

import { Log } from "../../util/Log.js";

const log = Log.create({ service: "cli.auth" });

// Auth storage (simple in-memory for now)
let authState = {
  provider: null,
  token: null,
  expires: null,
};

// Execute auth command
export const executeFFI = (args) => async () => {
  try {
    if (args.login) {
      const provider = args.provider || "default";
      return loginFFI(provider)();
    }
    
    if (args.logout) {
      return logoutFFI();
    }
    
    if (args.status) {
      return statusFFI();
    }
    
    return { tag: "Left", value: "No auth action specified (--login, --logout, or --status)" };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Login to a provider
export const loginFFI = (provider) => async () => {
  try {
    log.info("login", { provider });

    // Check for API key in environment based on provider
    var envKeys = {
      "anthropic": "ANTHROPIC_API_KEY",
      "openai": "OPENAI_API_KEY",
      "google": "GOOGLE_API_KEY",
      "default": "FORGE_API_KEY",
    };
    var envVar = envKeys[provider] || envKeys["default"];
    var token = process.env[envVar] || "";

    if (!token) {
      return { tag: "Left", value: "No API key found. Set " + envVar + " environment variable." };
    }

    authState = {
      provider,
      token: token,
      expires: Date.now() + 3600000, // 1 hour
    };

    console.log("Authenticated with " + provider);
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Logout
export const logoutFFI = async () => {
  try {
    log.info("logout");
    
    authState = {
      provider: null,
      token: null,
      expires: null,
    };
    
    console.log("Logged out");
    return { tag: "Right", value: undefined };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};

// Check auth status
export const statusFFI = async () => {
  try {
    log.info("status");
    
    if (!authState.token) {
      return {
        tag: "Right",
        value: JSON.stringify({ authenticated: false }),
      };
    }
    
    const isExpired = authState.expires && Date.now() > authState.expires;
    return {
      tag: "Right",
      value: JSON.stringify({
        authenticated: !isExpired,
        provider: authState.provider,
        expires: authState.expires,
      }),
    };
  } catch (err) {
    return { tag: "Left", value: err.message };
  }
};
