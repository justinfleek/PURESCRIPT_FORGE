-- | PureScript type definitions for OpenCode Session types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from opencode-dev/packages/opencode/src/session/
module Opencode.Types.Session where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.DateTime (DateTime)
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))

-- | Session identifier
type SessionID = String

-- | Project identifier
type ProjectID = String

-- | Session summary statistics
type SessionSummary =
  { additions :: Int
  , deletions :: Int
  , files :: Int
  , diffs :: Maybe (Array FileDiff)
  }

-- | File diff (placeholder - would import from Snapshot module)
type FileDiff = { path :: String, additions :: Int, deletions :: Int }

-- | Session share information
type ShareInfo =
  { url :: String
  }

-- | Session time information
type SessionTime =
  { created :: Number  -- Unix timestamp (milliseconds)
  , updated :: Number
  , compacting :: Maybe Number
  , archived :: Maybe Number
  }

-- | Session revert information
type RevertInfo =
  { messageID :: String
  , partID :: Maybe String
  , snapshot :: Maybe String
  , diff :: Maybe String
  }

-- | Permission ruleset (placeholder - would import from Permission module)
type PermissionRuleset = { allow :: Array String, deny :: Array String }

-- | Session information
type SessionInfo =
  { id :: SessionID
  , slug :: String
  , projectID :: ProjectID
  , directory :: String
  , parentID :: Maybe SessionID
  , summary :: Maybe SessionSummary
  , share :: Maybe ShareInfo
  , title :: String
  , version :: String
  , time :: SessionTime
  , permission :: Maybe PermissionRuleset
  , revert :: Maybe RevertInfo
  }

derive instance genericSessionInfo :: Generic SessionInfo _
derive instance eqSessionInfo :: Eq SessionInfo

instance showSessionInfo :: Show SessionInfo where
  show = genericShow

instance encodeJsonSessionInfo :: EncodeJson SessionInfo where
  encodeJson s = encodeJson
    { id: s.id
    , slug: s.slug
    , projectID: s.projectID
    , directory: s.directory
    , parentID: s.parentID
    , summary: s.summary
    , share: s.share
    , title: s.title
    , version: s.version
    , time: s.time
    , permission: s.permission
    , revert: s.revert
    }

instance decodeJsonSessionInfo :: DecodeJson SessionInfo where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    slug <- obj .: "slug"
    projectID <- obj .: "projectID"
    directory <- obj .: "directory"
    parentID <- obj .:? "parentID"
    summary <- obj .:? "summary"
    share <- obj .:? "share"
    title <- obj .: "title"
    version <- obj .: "version"
    time <- obj .: "time"
    permission <- obj .:? "permission"
    revert <- obj .:? "revert"
    pure { id, slug, projectID, directory, parentID, summary, share, title, version, time, permission, revert }

-- | Session share information (with secret)
type SessionShareInfo =
  { secret :: String
  , url :: String
  }

derive instance genericSessionShareInfo :: Generic SessionShareInfo _
derive instance eqSessionShareInfo :: Eq SessionShareInfo

instance showSessionShareInfo :: Show SessionShareInfo where
  show = genericShow

instance encodeJsonSessionShareInfo :: EncodeJson SessionShareInfo where
  encodeJson s = encodeJson { secret: s.secret, url: s.url }

instance decodeJsonSessionShareInfo :: DecodeJson SessionShareInfo where
  decodeJson json = do
    obj <- decodeJson json
    secret <- obj .: "secret"
    url <- obj .: "url"
    pure { secret, url }
