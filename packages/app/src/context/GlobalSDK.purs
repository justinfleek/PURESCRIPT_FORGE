-- | Global SDK context - manages global Forge client and event stream
-- | Migrated from: forge-dev/packages/app/src/context/global-sdk.tsx
module App.Context.GlobalSDK
  ( GlobalSDKContext
  , EventPayload(..)
  , QueuedEvent
  , mkGlobalSDKContext
  , eventKey
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Event payload types (simplified)
data EventPayload
  = SessionStatus { sessionID :: String }
  | LspUpdated
  | MessagePartUpdated { messageID :: String, partID :: String }
  | OtherEvent String

-- | Queued event
type QueuedEvent =
  { directory :: String
  , payload :: EventPayload
  }

-- | Global SDK context
type GlobalSDKContext =
  { url :: String
  }

-- | Create global SDK context
mkGlobalSDKContext :: String -> GlobalSDKContext
mkGlobalSDKContext url = { url }

-- | Generate key for event coalescing
eventKey :: String -> EventPayload -> Maybe String
eventKey directory payload =
  case payload of
    SessionStatus props ->
      Just $ "session.status:" <> directory <> ":" <> props.sessionID
    LspUpdated ->
      Just $ "lsp.updated:" <> directory
    MessagePartUpdated props ->
      Just $ "message.part.updated:" <> directory <> ":" <> props.messageID <> ":" <> props.partID
    OtherEvent _ ->
      Nothing
