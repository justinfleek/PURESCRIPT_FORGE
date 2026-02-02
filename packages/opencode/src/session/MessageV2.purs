-- | Session Message V2 - updated message format
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/session/message-v2.ts
module Opencode.Session.MessageV2 where

import Prelude
import Data.Maybe (Maybe)

-- | Message part types
data MessagePart
  = TextPart { text :: String }
  | ToolPart { tool :: String, input :: String, output :: Maybe String }
  | FilePart { path :: String, mime :: String }
  | ImagePart { url :: String, alt :: Maybe String }

-- | Message V2 format
type MessageV2 =
  { id :: String
  , sessionId :: String
  , role :: String
  , parts :: Array MessagePart
  , createdAt :: Number
  , updatedAt :: Maybe Number
  }
