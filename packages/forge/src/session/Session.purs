-- | Session management - core session operations
-- | 1:1 parity with opencode-dev/packages/opencode/src/session/index.ts
module Forge.Session.Session
  ( -- * Types
    SessionInfo
  , SessionTime
  , SessionShare
  , SessionSummary
  , SessionRevert
  , CreateInput
  , ForkInput
  , MessagesInput
  , RemoveMessageInput
  , RemovePartInput
  , InitializeInput
  , UsageInput
  , UsageResult
  , TokenUsage
  , CacheUsage
    -- * Events
  , Event
    -- * Core Operations
  , create
  , createNext
  , fork
  , touch
  , get
  , getShare
  , share
  , unshare
  , update
  , diff
  , messages
  , list
  , children
  , remove
  , plan
  , isDefaultTitle
    -- * Message Operations
  , updateMessage
  , removeMessage
  , updatePart
  , removePart
    -- * Utility
  , getUsage
  , initialize
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Session time metadata
type SessionTime =
  { created :: Number
  , updated :: Number
  , compacting :: Maybe Number
  , archived :: Maybe Number
  }

-- | Session share info
type SessionShare =
  { url :: String
  }

-- | Session summary info
type SessionSummary =
  { additions :: Int
  , deletions :: Int
  , files :: Int
  }

-- | Session revert info
type SessionRevert =
  { messageID :: String
  , partID :: Maybe String
  , snapshot :: Maybe String
  , diff :: Maybe String
  }

-- | Session information
type SessionInfo =
  { id :: String
  , slug :: String
  , projectID :: String
  , directory :: String
  , parentID :: Maybe String
  , summary :: Maybe SessionSummary
  , share :: Maybe SessionShare
  , title :: String
  , version :: String
  , time :: SessionTime
  , permission :: Foreign  -- PermissionNext.Ruleset
  , revert :: Maybe SessionRevert
  }

-- | Create session input
type CreateInput =
  { parentID :: Maybe String
  , title :: Maybe String
  , permission :: Foreign
  }

-- | Fork session input
type ForkInput =
  { sessionID :: String
  , messageID :: Maybe String
  }

-- | Messages query input
type MessagesInput =
  { sessionID :: String
  , limit :: Maybe Int
  }

-- | Remove message input
type RemoveMessageInput =
  { sessionID :: String
  , messageID :: String
  }

-- | Remove part input
type RemovePartInput =
  { sessionID :: String
  , messageID :: String
  , partID :: String
  }

-- | Initialize session input
type InitializeInput =
  { sessionID :: String
  , modelID :: String
  , providerID :: String
  , messageID :: String
  }

-- | Usage calculation input
type UsageInput =
  { model :: Foreign  -- Provider.Model
  , usage :: Foreign  -- LanguageModelUsage
  , metadata :: Maybe Foreign  -- ProviderMetadata
  }

-- | Cache usage
type CacheUsage =
  { read :: Int
  , write :: Int
  }

-- | Token usage
type TokenUsage =
  { input :: Int
  , output :: Int
  , reasoning :: Int
  , cache :: CacheUsage
  }

-- | Usage result
type UsageResult =
  { cost :: Number
  , tokens :: TokenUsage
  }

-- ============================================================================
-- EVENTS
-- ============================================================================

-- | Session events (FFI object)
foreign import data Event :: Type

-- ============================================================================
-- FFI IMPORTS
-- ============================================================================

-- | Create a new session
foreign import create :: Maybe CreateInput -> Aff (Either String SessionInfo)

-- | Create session with all options (internal)
foreign import createNext :: 
  { id :: Maybe String
  , title :: Maybe String
  , parentID :: Maybe String
  , directory :: String
  , permission :: Foreign
  } -> Aff SessionInfo

-- | Fork a session
foreign import fork :: ForkInput -> Aff (Either String SessionInfo)

-- | Touch session (update timestamp)
foreign import touch :: String -> Aff (Either String Unit)

-- | Get session plan file path
foreign import plan :: SessionInfo -> String

-- | Check if title is default
foreign import isDefaultTitle :: String -> Boolean

-- | Get session by ID
foreign import get :: String -> Aff (Either String (Maybe SessionInfo))

-- | Get session share info
foreign import getShare :: String -> Aff (Either String (Maybe SessionShare))

-- | Share a session
foreign import share :: String -> Aff (Either String SessionShare)

-- | Unshare a session
foreign import unshare :: String -> Aff (Either String Unit)

-- | Update session
foreign import update :: 
  String -> 
  (SessionInfo -> SessionInfo) -> 
  { touch :: Boolean } -> 
  Aff (Either String SessionInfo)

-- | Get session diff
foreign import diff :: String -> Aff (Either String (Array Foreign))

-- | Get session messages
foreign import messages :: MessagesInput -> Aff (Either String (Array Foreign))

-- | List all sessions (async generator wrapped as array)
foreign import listFFI :: Aff (Either String (Array SessionInfo))

-- | Alias for list
list :: Aff (Either String (Array SessionInfo))
list = listFFI

-- | Get children sessions
foreign import children :: String -> Aff (Either String (Array SessionInfo))

-- | Remove session
foreign import remove :: String -> Aff (Either String Unit)

-- | Update message
foreign import updateMessage :: Foreign -> Aff (Either String Foreign)

-- | Remove message
foreign import removeMessage :: RemoveMessageInput -> Aff (Either String String)

-- | Update part
foreign import updatePart :: Foreign -> Aff (Either String Foreign)

-- | Remove part
foreign import removePart :: RemovePartInput -> Aff (Either String String)

-- | Calculate usage/cost
foreign import getUsage :: UsageInput -> UsageResult

-- | Initialize session
foreign import initialize :: InitializeInput -> Aff (Either String Unit)
