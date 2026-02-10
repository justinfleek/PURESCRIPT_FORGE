-- | PureScript type definitions for Permission types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from opencode-dev/packages/opencode/src/permission/next.ts
module Forge.Permission where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Either (Either(..))
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))
import Foreign.Object (Object)

-- | Permission identifier
type PermissionID = String

-- | Session identifier
type SessionID = String

-- | Permission action
data PermissionAction = Allow | Deny | Ask

derive instance genericPermissionAction :: Generic PermissionAction _
derive instance eqPermissionAction :: Eq PermissionAction
derive instance ordPermissionAction :: Ord PermissionAction

instance showPermissionAction :: Show PermissionAction where
  show = genericShow

instance encodeJsonPermissionAction :: EncodeJson PermissionAction where
  encodeJson = case _ of
    Allow -> encodeJson "allow"
    Deny -> encodeJson "deny"
    Ask -> encodeJson "ask"

instance decodeJsonPermissionAction :: DecodeJson PermissionAction where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "allow" -> pure Allow
      "deny" -> pure Deny
      "ask" -> pure Ask
      _ -> Left "Invalid permission action"

-- | Permission rule
type PermissionRule =
  { permission :: String
  , pattern :: String
  , action :: PermissionAction
  }

instance encodeJsonPermissionRule :: EncodeJson { permission :: String, pattern :: String, action :: PermissionAction } where
  encodeJson r = encodeJson
    { permission: r.permission
    , pattern: r.pattern
    , action: r.action
    }

instance decodeJsonPermissionRule :: DecodeJson { permission :: String, pattern :: String, action :: PermissionAction } where
  decodeJson json = do
    obj <- decodeJson json
    permission <- obj .: "permission"
    pattern <- obj .: "pattern"
    action <- obj .: "action"
    pure { permission, pattern, action }

-- | Permission ruleset (array of rules)
type PermissionRuleset = Array PermissionRule

-- | Tool information (for permission requests)
type ToolInfo =
  { messageID :: String
  , callID :: String
  }

-- | Permission request
type PermissionRequest =
  { id :: PermissionID
  , sessionID :: SessionID
  , permission :: String
  , patterns :: Array String
  , metadata :: Object Json
  , always :: Array String
  , tool :: Maybe ToolInfo
  }

instance encodeJsonPermissionRequest :: EncodeJson PermissionRequest where
  encodeJson r = encodeJson
    { id: r.id
    , sessionID: r.sessionID
    , permission: r.permission
    , patterns: r.patterns
    , metadata: r.metadata
    , always: r.always
    , tool: r.tool
    }

instance decodeJsonPermissionRequest :: DecodeJson PermissionRequest where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    sessionID <- obj .: "sessionID"
    permission <- obj .: "permission"
    patterns <- obj .: "patterns"
    metadata <- obj .: "metadata"
    always <- obj .: "always"
    tool <- obj .:? "tool"
    pure { id, sessionID, permission, patterns, metadata, always, tool }

-- | Permission reply
data PermissionReply = Once | Always | Reject

derive instance genericPermissionReply :: Generic PermissionReply _
derive instance eqPermissionReply :: Eq PermissionReply

instance showPermissionReply :: Show PermissionReply where
  show = genericShow

instance encodeJsonPermissionReply :: EncodeJson PermissionReply where
  encodeJson = case _ of
    Once -> encodeJson "once"
    Always -> encodeJson "always"
    Reject -> encodeJson "reject"

instance decodeJsonPermissionReply :: DecodeJson PermissionReply where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "once" -> pure Once
      "always" -> pure Always
      "reject" -> pure Reject
      _ -> Left "Invalid permission reply"

-- | Permission approval
type PermissionApproval =
  { projectID :: String
  , patterns :: Array String
  }
