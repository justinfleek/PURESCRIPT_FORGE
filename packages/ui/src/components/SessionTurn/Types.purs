-- | SessionTurn Types Module
-- | Shared types for session turn rendering.
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/session-turn.tsx

module UI.Components.SessionTurn.Types
  ( SessionStatus(..)
  , SessionTurnProps
  , SessionTurnClasses
  , FileDiff
  , PermissionPart
  ) where

import Prelude

import Data.Maybe (Maybe)
import Effect (Effect)
import UI.Components.MessagePart.Types (Message, Part, ToolPartData, AssistantMessage)

-- ═══════════════════════════════════════════════════════════════════════════════
-- SESSION STATUS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Session execution status
data SessionStatus
  = Idle
  | Running
  | Retry { message :: String, next :: Maybe Number, attempt :: Int }

derive instance eqSessionStatus :: Eq SessionStatus

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROPS TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS class overrides
type SessionTurnClasses =
  { root :: Maybe String
  , content :: Maybe String
  , container :: Maybe String
  }

-- | Session turn component props
type SessionTurnProps =
  { sessionID :: String
  , sessionTitle :: Maybe String
  , messageID :: String
  , lastUserMessageID :: Maybe String
  , stepsExpanded :: Boolean
  , onStepsExpandedToggle :: Maybe (Effect Unit)
  , onUserInteracted :: Maybe (Effect Unit)
  , classes :: Maybe SessionTurnClasses
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- HELPER TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | File diff from message summary
type FileDiff =
  { file :: String
  , before :: Maybe String
  , after :: Maybe String
  , additions :: Int
  , deletions :: Int
  }

-- | Permission part with message context
type PermissionPart =
  { part :: ToolPartData
  , message :: AssistantMessage
  }
