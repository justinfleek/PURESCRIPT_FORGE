-- | PureScript type definitions for OpenCode Message types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from opencode-dev/packages/opencode/src/session/message.ts
module Opencode.Types.Message where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Either (Either(..))
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))
import Data.Argonaut.Decode.Error (JsonDecodeError(..))

-- | Message role
data MessageRole = User | Assistant

derive instance genericMessageRole :: Generic MessageRole _
derive instance eqMessageRole :: Eq MessageRole
derive instance ordMessageRole :: Ord MessageRole

instance showMessageRole :: Show MessageRole where
  show = genericShow

instance encodeJsonMessageRole :: EncodeJson MessageRole where
  encodeJson = case _ of
    User -> encodeJson "user"
    Assistant -> encodeJson "assistant"

instance decodeJsonMessageRole :: DecodeJson MessageRole where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "user" -> pure User
      "assistant" -> pure Assistant
      _ -> Left (UnexpectedValue json)

-- | Message part type
data MessagePartType = Text | Code | Diff | Bash | Error | Markdown

derive instance genericMessagePartType :: Generic MessagePartType _
derive instance eqMessagePartType :: Eq MessagePartType

instance showMessagePartType :: Show MessagePartType where
  show = genericShow

-- | Message part
type MessagePart =
  { partType :: MessagePartType
  , content :: String
  , language :: Maybe String
  , path :: Maybe String
  }

-- | Message time metadata
type MessageTime =
  { created :: Number  -- Unix timestamp (milliseconds)
  , completed :: Maybe Number
  }

-- | Token usage information
type TokenUsage =
  { input :: Int
  , output :: Int
  , reasoning :: Int
  , cacheRead :: Int
  , cacheWrite :: Int
  }

-- | Assistant metadata
type AssistantMetadata =
  { system :: Array String
  , modelID :: String
  , providerID :: String
  , cwd :: String
  , root :: String
  , cost :: Number
  , summary :: Maybe Boolean
  , tokens :: TokenUsage
  }

-- | Tool execution metadata
type ToolMetadata =
  { title :: String
  , snapshot :: Maybe String
  , timeStart :: Number
  , timeEnd :: Number
  }

-- | Error types (simplified)
data MessageError = AuthError String | UnknownError String | OutputLengthError String

derive instance genericMessageError :: Generic MessageError _
derive instance eqMessageError :: Eq MessageError

instance showMessageError :: Show MessageError where
  show = genericShow

-- | Message metadata
type MessageMetadata =
  { created :: Number
  , completed :: Maybe Number
  , error :: Maybe String
  , sessionID :: String
  , snapshot :: Maybe String
  }

-- | Message information
type MessageInfo =
  { id :: String
  , role :: MessageRole
  , parts :: Array MessagePart
  , metadata :: MessageMetadata
  }
