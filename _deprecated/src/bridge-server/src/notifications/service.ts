/**
 * Notification Service
 * 
 * Manages toast notifications, banners, and system messages.
 * Broadcasts notifications to all connected WebSocket clients.
 * 
 * Spec: 36-NOTIFICATION-SYSTEM
 */
import { WebSocketManager } from "../websocket/manager.js";
import pino from "pino";

const logger = pino({ name: "notification-service" });

export type NotificationType = "toast" | "banner" | "inline" | "silent";
export type NotificationLevel = "success" | "info" | "warning" | "error";

export interface NotificationAction {
  label: string;
  actionId: string;
  primary?: boolean;
}

export interface Notification {
  id: string;
  type: NotificationType;
  level: NotificationLevel;
  title: string;
  message?: string;
  createdAt: string; // ISO timestamp
  duration?: number; // milliseconds, undefined = persistent
  actions?: NotificationAction[];
  dismissible: boolean;
  persistent: boolean;
  group?: string;
  replaceExisting?: boolean;
}

export interface NotificationConfig {
  maxToasts: number;
  defaultDuration: number;
  position: "top-right" | "top-left" | "bottom-right" | "bottom-left";
  enableSound: boolean;
}

/**
 * Notification Service
 * 
 * Provides methods to show notifications and broadcasts them to clients
 */
export class NotificationService {
  private wsManager: WebSocketManager;
  private config: NotificationConfig;
  private notificationIdCounter = 0;
  
  constructor(
    wsManager: WebSocketManager,
    config?: Partial<NotificationConfig>
  ) {
    this.wsManager = wsManager;
    this.config = {
      maxToasts: config?.maxToasts ?? 5,
      defaultDuration: config?.defaultDuration ?? 4000,
      position: config?.position ?? "bottom-right",
      enableSound: config?.enableSound ?? false,
      ...config,
    };
  }
  
  /**
   * Generate unique notification ID
   */
  private generateId(): string {
    this.notificationIdCounter++;
    return `notification-${Date.now()}-${this.notificationIdCounter}`;
  }
  
  /**
   * Get default duration for notification level
   */
  private getDefaultDuration(level: NotificationLevel): number {
    switch (level) {
      case "error":
        return 8000;
      case "warning":
        return 5000;
      case "success":
        return 3000;
      case "info":
      default:
        return 4000;
    }
  }
  
  /**
   * Show a notification
   */
  notify(notification: Partial<Notification>): void {
    const full: Notification = {
      id: notification.id ?? this.generateId(),
      type: notification.type ?? "toast",
      level: notification.level ?? "info",
      title: notification.title ?? "",
      message: notification.message,
      createdAt: notification.createdAt ?? new Date().toISOString(),
      duration: notification.duration ?? this.getDefaultDuration(notification.level ?? "info"),
      actions: notification.actions ?? [],
      dismissible: notification.dismissible ?? true,
      persistent: notification.persistent ?? false,
      group: notification.group,
      replaceExisting: notification.replaceExisting,
    };
    
    logger.info("Showing notification", {
      id: full.id,
      type: full.type,
      level: full.level,
      title: full.title,
    });
    
    // Broadcast to all connected clients
    this.wsManager.broadcast({
      jsonrpc: "2.0",
      method: "notification.show",
      params: full,
    });
  }
  
  /**
   * Convenience method: Success toast
   */
  success(title: string, message?: string): void {
    this.notify({
      level: "success",
      type: "toast",
      title,
      message,
      duration: 3000,
    });
  }
  
  /**
   * Convenience method: Success toast with action
   */
  successWithAction(
    title: string,
    message: string,
    actionLabel: string,
    actionId: string
  ): void {
    this.notify({
      level: "success",
      type: "toast",
      title,
      message,
      duration: 5000,
      actions: [{ label: actionLabel, actionId, primary: true }],
    });
  }
  
  /**
   * Convenience method: Warning toast
   */
  warning(title: string, message?: string): void {
    this.notify({
      level: "warning",
      type: "toast",
      title,
      message,
      duration: 5000,
    });
  }
  
  /**
   * Convenience method: Error toast
   */
  error(title: string, message?: string): void {
    this.notify({
      level: "error",
      type: "toast",
      title,
      message,
      duration: 8000,
    });
  }
  
  /**
   * Convenience method: Error banner (persistent)
   */
  errorBanner(title: string, message?: string): void {
    this.notify({
      level: "error",
      type: "banner",
      title,
      message,
      persistent: true,
      dismissible: true,
    });
  }
  
  /**
   * Convenience method: Info toast
   */
  info(title: string, message?: string): void {
    this.notify({
      level: "info",
      type: "toast",
      title,
      message,
      duration: 4000,
    });
  }
  
  /**
   * Notify about low Diem balance
   */
  notifyLowBalance(diem: number): void {
    if (diem < 5) {
      this.notify({
        type: "banner",
        level: "error",
        title: "Critical: Balance below 5 Diem",
        message: `Only ${diem.toFixed(1)} Diem remaining. You may run out before reset.`,
        persistent: true,
        dismissible: true,
        actions: [
          {
            label: "View Usage",
            actionId: "navigate-performance",
            primary: false,
          },
        ],
      });
    } else if (diem < 10) {
      this.notify({
        level: "warning",
        type: "toast",
        title: "Balance below 10 Diem",
        message: "Consider slowing down to make it to reset.",
        duration: 5000,
      });
    }
  }
  
  /**
   * Notify about connection status
   */
  notifyConnectionLost(): void {
    this.notify({
      level: "error",
      type: "toast",
      title: "Connection lost",
      message: "Attempting to reconnect...",
      duration: 5000,
      actions: [
        {
          label: "Retry",
          actionId: "reconnect",
          primary: true,
        },
      ],
    });
  }
  
  /**
   * Notify about connection restored
   */
  notifyConnectionRestored(): void {
    this.success("Connection restored");
  }
  
  /**
   * Notify about session export
   */
  notifySessionExported(filename: string): void {
    this.successWithAction(
      "Session exported successfully",
      `${filename} saved to Downloads`,
      "View",
      `open-file-${filename}`
    );
  }
  
  /**
   * Notify about snapshot creation
   */
  notifySnapshotCreated(snapshotId: string): void {
    this.success("Snapshot created", `Snapshot ID: ${snapshotId}`);
  }
  
  /**
   * Notify about proof completion
   */
  notifyProofComplete(theorem: string): void {
    this.success("Proof complete", `Theorem "${theorem}" verified`);
  }
  
  /**
   * Dismiss a notification
   */
  dismiss(notificationId: string): void {
    this.wsManager.broadcast({
      jsonrpc: "2.0",
      method: "notification.dismiss",
      params: { id: notificationId },
    });
  }
  
  /**
   * Dismiss all notifications
   */
  dismissAll(): void {
    this.wsManager.broadcast({
      jsonrpc: "2.0",
      method: "notification.dismissAll",
      params: {},
    });
  }
}
