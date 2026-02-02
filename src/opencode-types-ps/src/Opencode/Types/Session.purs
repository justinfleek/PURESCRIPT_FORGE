-- | PureScript type definitions for OpenCode Session types
-- | Phase 2: Type Safety Layer
module Opencode.Types.Session where

import Prelude
import Data.Maybe (Maybe)
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, (.:), (.:?))

-- | Session identifier
type SessionID = String

-- | Project identifier
type ProjectID = String

-- | File diff
type FileDiff = 
  { path :: String
  , additions :: Int
  , deletions :: Int 
  }

-- | Session summary statistics
type SessionSummary =
  { additions :: Int
  , deletions :: Int
  , files :: Int
  }

-- | Session share information
type ShareInfo =
  { url :: String
  }

-- | Session time information
type SessionTime =
  { created :: Number
  , updated :: Number
  }

-- | Session revert information
type RevertInfo =
  { messageID :: String
  , partID :: Maybe String
  , snapshot :: Maybe String
  }

-- | Session information
type SessionInfo =
  { id :: SessionID
  , slug :: String
  , projectID :: ProjectID
  , directory :: String
  , parentID :: Maybe SessionID
  , title :: String
  , version :: String
  , created :: Number
  , updated :: Number
  }

-- | Session share information (with secret)
type SessionShareInfo =
  { secret :: String
  , url :: String
  }
