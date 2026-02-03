-- | PureScript type definitions for Forge Permission types
-- | Phase 2: Type Safety Layer
module Forge.Types.Permission where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Either (Either(..))
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))
import Data.Argonaut.Decode.Error (JsonDecodeError(..))

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
      _ -> Left (UnexpectedValue json)

-- | Permission rule
type PermissionRule =
  { permission :: String
  , pattern :: String
  , action :: PermissionAction
  }

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
  , always :: Array String
  , tool :: Maybe ToolInfo
  }

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
      _ -> Left (UnexpectedValue json)

-- | Permission approval
type PermissionApproval =
  { projectID :: String
  , patterns :: Array String
  }
