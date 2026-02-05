# 36-NOTIFICATION-SYSTEM: Toasts, Alerts, and System Messages

## Overview

The Notification System provides non-blocking feedback for user actions, system events, and important alerts through toast notifications, persistent banners, and in-app messages.

---

## Notification Types

| Type | Duration | Position | Use Case |
|------|----------|----------|----------|
| Toast | 3-5s | Bottom-right | Action confirmations |
| Alert Banner | Until dismissed | Top | System warnings |
| Persistent | Until action | Inline | Requires user action |
| Silent | None | Badge only | Background updates |

---

## Visual Design

### Toast Notifications

```
                                    ┌──────────────────────────────────────┐
                                    │  ✓ Session exported successfully     │
                                    │                                      │
                                    │  debug-auth.md saved to Downloads    │
                                    │                             [View]   │
                                    └──────────────────────────────────────┘

                                    ┌──────────────────────────────────────┐
                                    │  ⚠ Balance below 10 Diem             │
                                    │                                      │
                                    │  Consider slowing down to make       │
                                    │  it to reset.            [Dismiss]   │
                                    └──────────────────────────────────────┘

                                    ┌──────────────────────────────────────┐
                                    │  ✕ Connection lost                   │
                                    │                                      │
                                    │  Attempting to reconnect...          │
                                    │                            [Retry]   │
                                    └──────────────────────────────────────┘
```

### Toast Stack (Multiple)

```
                                    ┌──────────────────────────────────────┐
                                    │  ✓ Snapshot created                  │
                                    └──────────────────────────────────────┘
                                    ┌──────────────────────────────────────┐
                                    │  ✓ Branch "try-hooks" created        │
                                    └──────────────────────────────────────┘
                                    ┌──────────────────────────────────────┐
                                    │  ⚠ File context exceeds 50K tokens   │
                                    │                           [Manage]   │
                                    └──────────────────────────────────────┘
```

### Alert Banner

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  ⚠ Your Diem balance is critically low (2.3 Diem remaining)    [Dismiss]   │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Persistent Notification (Inline)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─ ACTION REQUIRED ─────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  🔄 Session recovered from crash                                      │ │
│  │                                                                        │ │
│  │  We found an unsaved session from 10 minutes ago.                     │ │
│  │  Would you like to restore it?                                        │ │
│  │                                                                        │ │
│  │  [Restore Session]  [Discard]  [View Details]                         │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface Notification {
  id: string;
  type: NotificationType;
  level: NotificationLevel;
  title: string;
  message?: string;
  
  // Timing
  createdAt: Date;
  duration?: number;  // ms, undefined = persistent
  
  // Actions
  actions?: NotificationAction[];
  onDismiss?: () => void;
  
  // Behavior
  dismissible: boolean;
  persistent: boolean;
  
  // Grouping
  group?: string;
  replaceExisting?: boolean;
}

type NotificationType = 
  | 'toast'
  | 'banner'
  | 'inline'
  | 'silent';

type NotificationLevel =
  | 'success'
  | 'info'
  | 'warning'
  | 'error';

interface NotificationAction {
  label: string;
  action: () => void;
  primary?: boolean;
}

interface NotificationConfig {
  maxToasts: number;
  defaultDuration: number;
  position: ToastPosition;
  enableSound: boolean;
}

type ToastPosition = 
  | 'top-right'
  | 'top-left'
  | 'bottom-right'
  | 'bottom-left';
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Notifications where

import Prelude
import Data.Array (Array)
import Data.Maybe (Maybe)
import Data.DateTime (DateTime)

data NotificationType
  = Toast
  | Banner
  | Inline
  | Silent

data NotificationLevel
  = Success
  | Info
  | Warning
  | Error

type NotificationAction =
  { label :: String
  , actionId :: String
  , primary :: Boolean
  }

type Notification =
  { id :: String
  , notificationType :: NotificationType
  , level :: NotificationLevel
  , title :: String
  , message :: Maybe String
  , createdAt :: DateTime
  , duration :: Maybe Int
  , actions :: Array NotificationAction
  , dismissible :: Boolean
  , persistent :: Boolean
  }

type NotificationState =
  { toasts :: Array Notification
  , banner :: Maybe Notification
  , inlineNotifications :: Array Notification
  , unreadCount :: Int
  }

data Action
  = Show Notification
  | Dismiss String
  | DismissAll
  | ExecuteAction String String  -- notification ID, action ID
  | ClearExpired
```

### Notification Service

```purescript
module Sidepanel.Services.Notifications where

-- Show a success toast
success :: String -> Effect Unit
success title = showToast
  { level: Success
  , title
  , message: Nothing
  , duration: Just 3000
  }

-- Show a success toast with message
successWithMessage :: String -> String -> Effect Unit
successWithMessage title message = showToast
  { level: Success
  , title
  , message: Just message
  , duration: Just 5000
  }

-- Show a warning toast
warning :: String -> Effect Unit
warning title = showToast
  { level: Warning
  , title
  , message: Nothing
  , duration: Just 5000
  }

-- Show an error toast (longer duration)
error :: String -> String -> Effect Unit
error title message = showToast
  { level: Error
  , title
  , message: Just message
  , duration: Just 8000
  }

-- Show a persistent error banner
errorBanner :: String -> String -> Effect Unit
errorBanner title message = showBanner
  { level: Error
  , title
  , message: Just message
  , persistent: true
  }

-- Show toast with action
successWithAction :: String -> String -> String -> (Unit -> Effect Unit) -> Effect Unit
successWithAction title message actionLabel action = showToast
  { level: Success
  , title
  , message: Just message
  , duration: Just 5000
  , actions: [{ label: actionLabel, action, primary: true }]
  }
```

### Toast Container Component

```purescript
module Sidepanel.Components.ToastContainer where

component :: forall q m. MonadAff m => H.Component q NotificationState Output m
component = H.mkComponent
  { initialState: identity
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction }
  }

render :: forall m. NotificationState -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "toast-container") ]
    (map renderToast state.toasts)

renderToast :: forall m. Notification -> H.ComponentHTML Action () m
renderToast notification =
  HH.div
    [ HP.classes $ toastClasses notification.level
    , HP.key notification.id
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "toast__icon") ]
        [ HH.text $ levelIcon notification.level ]
    , HH.div
        [ HP.class_ (H.ClassName "toast__content") ]
        [ HH.div
            [ HP.class_ (H.ClassName "toast__title") ]
            [ HH.text notification.title ]
        , case notification.message of
            Just msg ->
              HH.div
                [ HP.class_ (H.ClassName "toast__message") ]
                [ HH.text msg ]
            Nothing -> HH.text ""
        ]
    , when (not (null notification.actions)) $
        HH.div
          [ HP.class_ (H.ClassName "toast__actions") ]
          (map (renderAction notification.id) notification.actions)
    , when notification.dismissible $
        HH.button
          [ HP.class_ (H.ClassName "toast__dismiss")
          , HE.onClick \_ -> Dismiss notification.id
          ]
          [ HH.text "✕" ]
    ]

renderAction :: forall m. String -> NotificationAction -> H.ComponentHTML Action () m
renderAction notificationId action =
  HH.button
    [ HP.classes $ actionClasses action.primary
    , HE.onClick \_ -> ExecuteAction notificationId action.actionId
    ]
    [ HH.text action.label ]

levelIcon :: NotificationLevel -> String
levelIcon = case _ of
  Success -> "✓"
  Info -> "ℹ"
  Warning -> "⚠"
  Error -> "✕"

toastClasses :: NotificationLevel -> Array H.ClassName
toastClasses level =
  [ H.ClassName "toast"
  , H.ClassName $ "toast--" <> levelToString level
  ]
```

---

## Bridge Integration

```typescript
// bridge/src/notifications/service.ts

export class NotificationService {
  private wsManager: WebSocketManager;
  
  // Broadcast notification to all connected clients
  notify(notification: Partial<Notification>): void {
    const full: Notification = {
      id: generateId(),
      type: notification.type ?? 'toast',
      level: notification.level ?? 'info',
      title: notification.title ?? '',
      message: notification.message,
      createdAt: new Date(),
      duration: notification.duration ?? this.getDefaultDuration(notification.level),
      actions: notification.actions ?? [],
      dismissible: notification.dismissible ?? true,
      persistent: notification.persistent ?? false
    };
    
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'notification.show',
      params: full
    });
  }
  
  private getDefaultDuration(level?: NotificationLevel): number {
    switch (level) {
      case 'error': return 8000;
      case 'warning': return 5000;
      case 'success': return 3000;
      default: return 4000;
    }
  }
  
  // Convenience methods
  success(title: string, message?: string): void {
    this.notify({ level: 'success', title, message });
  }
  
  warning(title: string, message?: string): void {
    this.notify({ level: 'warning', title, message });
  }
  
  error(title: string, message?: string): void {
    this.notify({ level: 'error', title, message });
  }
  
  // Balance-specific notifications
  notifyLowBalance(diem: number): void {
    if (diem < 5) {
      this.notify({
        type: 'banner',
        level: 'error',
        title: 'Critical: Balance below 5 Diem',
        message: `Only ${diem.toFixed(1)} Diem remaining. You may run out before reset.`,
        persistent: true,
        actions: [
          { label: 'View Usage', action: () => navigate('/performance'), primary: false }
        ]
      });
    } else if (diem < 10) {
      this.notify({
        level: 'warning',
        title: 'Balance below 10 Diem',
        message: 'Consider slowing down to make it to reset.',
        duration: 5000
      });
    }
  }
}
```

---

## CSS Styling

```css
.toast-container {
  position: fixed;
  bottom: var(--space-4);
  right: var(--space-4);
  display: flex;
  flex-direction: column-reverse;
  gap: var(--space-2);
  z-index: 1000;
  max-width: 380px;
}

.toast {
  display: flex;
  align-items: flex-start;
  gap: var(--space-3);
  padding: var(--space-3) var(--space-4);
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-default);
  border-radius: 8px;
  box-shadow: var(--shadow-lg);
  animation: slideIn 0.2s ease-out;
}

.toast--exiting {
  animation: slideOut 0.2s ease-in forwards;
}

@keyframes slideIn {
  from {
    opacity: 0;
    transform: translateX(100%);
  }
  to {
    opacity: 1;
    transform: translateX(0);
  }
}

@keyframes slideOut {
  from {
    opacity: 1;
    transform: translateX(0);
  }
  to {
    opacity: 0;
    transform: translateX(100%);
  }
}

.toast--success {
  border-left: 4px solid var(--color-success);
}

.toast--success .toast__icon {
  color: var(--color-success);
}

.toast--warning {
  border-left: 4px solid var(--color-warning);
}

.toast--warning .toast__icon {
  color: var(--color-warning);
}

.toast--error {
  border-left: 4px solid var(--color-error);
}

.toast--error .toast__icon {
  color: var(--color-error);
}

.toast--info {
  border-left: 4px solid var(--color-info);
}

.toast--info .toast__icon {
  color: var(--color-info);
}

.toast__icon {
  font-size: 18px;
  flex-shrink: 0;
  margin-top: 2px;
}

.toast__content {
  flex: 1;
  min-width: 0;
}

.toast__title {
  font-weight: var(--font-weight-medium);
  color: var(--color-text-primary);
  margin-bottom: var(--space-1);
}

.toast__message {
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
}

.toast__actions {
  display: flex;
  gap: var(--space-2);
  margin-top: var(--space-2);
}

.toast__dismiss {
  position: absolute;
  top: var(--space-2);
  right: var(--space-2);
  background: none;
  border: none;
  color: var(--color-text-tertiary);
  cursor: pointer;
  padding: var(--space-1);
  font-size: 12px;
}

/* Banner */
.notification-banner {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  padding: var(--space-2) var(--space-4);
  display: flex;
  align-items: center;
  gap: var(--space-3);
  z-index: 1001;
  animation: slideDown 0.2s ease-out;
}

.notification-banner--warning {
  background: var(--color-warning-dim);
  border-bottom: 1px solid var(--color-warning);
}

.notification-banner--error {
  background: var(--color-error-dim);
  border-bottom: 1px solid var(--color-error);
}
```

---

## Notification Events

| Event | Notification |
|-------|--------------|
| Session exported | Success toast |
| Snapshot created | Success toast |
| Branch created | Success toast |
| Balance < 10 Diem | Warning toast |
| Balance < 5 Diem | Error banner |
| Connection lost | Error toast + retry |
| Session restored | Info with action |
| Proof complete | Success toast |

---

## Related Specifications

- `56-ALERT-SYSTEM.md` - Balance alerts
- `35-CONNECTION-STATUS.md` - Connection notifications
- `47-THEMING.md` - Color tokens

---

*"Good feedback is instant, clear, and actionable."*
