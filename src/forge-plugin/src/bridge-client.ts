/**
 * Bridge Client
 * 
 * WebSocket client for communicating with Bridge Server
 */
import WebSocket from "ws";
import pino from "pino";

const logger = pino({ name: "bridge-client" });

interface BridgeMessage {
  jsonrpc: "2.0";
  method: string;
  params?: Record<string, unknown>;
  id?: string | number;
}

export class BridgeClient {
  private url: string;
  private ws: WebSocket | null = null;
  private reconnectAttempts = 0;
  private maxReconnectAttempts = 10;
  private reconnectDelay = 1000;
  private connected = false;
  
  constructor(url: string) {
    this.url = url.replace(/^http/, "ws") + "/ws";
  }
  
  /**
   * Connect to Bridge Server
   */
  async connect(): Promise<void> {
    return new Promise((resolve, reject) => {
      try {
        this.ws = new WebSocket(this.url);
        
        this.ws.on("open", () => {
          logger.info("Connected to Bridge Server", { url: this.url });
          this.connected = true;
          this.reconnectAttempts = 0;
          resolve();
        });
        
        this.ws.on("error", (error) => {
          logger.error("WebSocket error", { error: error.message });
          if (!this.connected) {
            reject(error);
          }
        });
        
        this.ws.on("close", () => {
          logger.warn("WebSocket closed");
          this.connected = false;
          this.attemptReconnect();
        });
        
        this.ws.on("message", (data) => {
          try {
            const message = JSON.parse(data.toString()) as BridgeMessage;
            this.handleMessage(message);
          } catch (error) {
            logger.error("Failed to parse message", { error });
          }
        });
      } catch (error) {
        reject(error);
      }
    });
  }
  
  /**
   * Attempt to reconnect with exponential backoff
   */
  private attemptReconnect(): void {
    if (this.reconnectAttempts >= this.maxReconnectAttempts) {
      logger.error("Max reconnect attempts reached");
      return;
    }
    
    this.reconnectAttempts++;
    const delay = this.reconnectDelay * Math.pow(2, this.reconnectAttempts - 1);
    
    logger.info("Attempting reconnect", { 
      attempt: this.reconnectAttempts, 
      delay 
    });
    
    setTimeout(() => {
      this.connect().catch((error) => {
        logger.error("Reconnect failed", { error });
      });
    }, delay);
  }
  
  /**
   * Handle incoming message from Bridge Server
   */
  private handleMessage(message: BridgeMessage): void {
    switch (message.method) {
      case "ping":
        this.send({ jsonrpc: "2.0", method: "pong" });
        break;
      default:
        logger.debug("Received message", { method: message.method });
    }
  }
  
  /**
   * Send message to Bridge Server
   */
  private send(message: BridgeMessage): void {
    if (!this.ws || this.ws.readyState !== WebSocket.OPEN) {
      logger.warn("WebSocket not connected, cannot send message");
      return;
    }
    
    try {
      this.ws.send(JSON.stringify(message));
    } catch (error) {
      logger.error("Failed to send message", { error });
    }
  }
  
  /**
   * Send Forge event to Bridge Server
   */
  async sendEvent(event: ForgeEvent): Promise<void> {
    this.send({
      jsonrpc: "2.0",
      method: "forge.event",
      params: { event },
    });
  }
  
  /**
   * Send chat message to Bridge Server
   */
  async sendMessage(message: {
    sessionID: string;
    messageID?: string;
    agent?: string;
    model?: { providerID: string; modelID: string };
    message: unknown;
    parts: unknown[];
  }): Promise<void> {
    this.send({
      jsonrpc: "2.0",
      method: "forge.message",
      params: message,
    });
  }
  
  /**
   * Send tool execution to Bridge Server
   */
  async sendToolExecution(execution: {
    tool: string;
    sessionID: string;
    callID: string;
    title: string;
    output: string;
    metadata: unknown;
  }): Promise<void> {
    this.send({
      jsonrpc: "2.0",
      method: "forge.tool.execution",
      params: execution,
    });
  }
  
  /**
   * Send config to Bridge Server
   */
  async sendConfig(config: ForgeConfig): Promise<void> {
    this.send({
      jsonrpc: "2.0",
      method: "forge.config",
      params: { config },
    });
  }
  
  /**
   * Disconnect from Bridge Server
   */
  disconnect(): void {
    if (this.ws) {
      this.ws.close();
      this.ws = null;
      this.connected = false;
    }
  }
}
