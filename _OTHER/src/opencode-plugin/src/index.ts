/**
 * OpenCode Sidepanel Plugin
 * 
 * This plugin integrates OpenCode with the Bridge Server, forwarding all events
 * to enable real-time sidepanel updates.
 * 
 * Spec: 21-PLUGIN-SYSTEM
 */
import type { Hooks, PluginInput, Event } from "@opencode-ai/plugin";
import { BridgeClient } from "./bridge-client.js";
import pino from "pino";
import type { OpenCodeEvent, OpenCodeConfig } from "./opencode-types.js";

const logger = pino({ name: "opencode-sidepanel-plugin" });

/**
 * OpenCode Sidepanel Plugin
 * 
 * Connects to Bridge Server and forwards all OpenCode events
 */
export async function SidepanelPlugin(input: PluginInput): Promise<Hooks> {
  logger.info("Initializing OpenCode Sidepanel Plugin");
  
  // Get bridge server URL from config or environment
  const bridgeUrl = process.env.BRIDGE_SERVER_URL ?? "http://localhost:8765";
  
  // Create bridge client
  const bridgeClient = new BridgeClient(bridgeUrl);
  
  let connected = false;
  
  try {
    await bridgeClient.connect();
    connected = true;
    logger.info("Connected to Bridge Server", { bridgeUrl });
  } catch (error) {
    logger.error("Failed to connect to Bridge Server", { 
      bridgeUrl, 
      error: error instanceof Error ? error.message : String(error) 
    });
    // Return no-op hooks if connection fails (graceful degradation)
    return {};
  }
  
  // Return event hooks
  return {
    /**
     * Main event hook - receives all OpenCode events
     */
    event: async ({ event }: { event: Event }) => {
      if (!connected) return;
      
      try {
        // Forward event to Bridge Server (typed as OpenCodeEvent)
        await bridgeClient.sendEvent(event as OpenCodeEvent);
      } catch (error) {
        logger.error("Failed to forward event to Bridge Server", {
          eventType: event.type,
          error: error instanceof Error ? error.message : String(error),
        });
      }
    },
    
    /**
     * Chat message hook - track message completion for token usage
     */
    "chat.message": async (input, output) => {
      if (!connected) return;
      
      try {
        await bridgeClient.sendMessage({
          sessionID: input.sessionID,
          messageID: input.messageID,
          agent: input.agent,
          model: input.model,
          message: output.message,
          parts: output.parts,
        });
      } catch (error) {
        logger.error("Failed to forward chat message", {
          sessionID: input.sessionID,
          error: error instanceof Error ? error.message : String(error),
        });
      }
    },
    
    /**
     * Tool execution hook - track tool usage for performance profiling
     */
    "tool.execute.after": async (input, output) => {
      if (!connected) return;
      
      try {
        await bridgeClient.sendToolExecution({
          tool: input.tool,
          sessionID: input.sessionID,
          callID: input.callID,
          title: output.title,
          output: output.output,
          metadata: output.metadata,
        });
      } catch (error) {
        logger.error("Failed to forward tool execution", {
          tool: input.tool,
          sessionID: input.sessionID,
          error: error instanceof Error ? error.message : String(error),
        });
      }
    },
    
    /**
     * Config hook - notify Bridge Server of config changes
     */
    config: async (config) => {
      if (!connected) return;
      
      try {
        await bridgeClient.sendConfig(config as OpenCodeConfig);
      } catch (error) {
        logger.error("Failed to forward config", {
          error: error instanceof Error ? error.message : String(error),
        });
      }
    },
  };
}

// Default export for convenience
export default SidepanelPlugin;
