-- | PureScript type definitions for OpenCode Message types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from opencode-dev/packages/opencode/src/session/message.ts
module Opencode.Types.Message where

import Prelude

import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))
import Data.Argonaut.Decode.Error (JsonDecodeError(TypeMismatch))
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Foreign.Object (Object)

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
      _ -> Left (TypeMismatch "Invalid message role")

-- | Message part type
data MessagePartType = Text | Code | Diff | Bash | Error | Markdown

derive instance genericMessagePartType :: Generic MessagePartType _
derive instance eqMessagePartType :: Eq MessagePartType

instance showMessagePartType :: Show MessagePartType where
  show = genericShow

instance encodeJsonMessagePartType :: EncodeJson MessagePartType where
  encodeJson = case _ of
    Text -> encodeJson "text"
    Code -> encodeJson "code"
    Diff -> encodeJson "diff"
    Bash -> encodeJson "bash"
    Error -> encodeJson "error"
    Markdown -> encodeJson "markdown"

instance decodeJsonMessagePartType :: DecodeJson MessagePartType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "text" -> pure Text
      "code" -> pure Code
      "diff" -> pure Diff
      "bash" -> pure Bash
      "error" -> pure Error
      "markdown" -> pure Markdown
      _ -> Left (TypeMismatch "Invalid message part type")

-- | Message part
type MessagePart =
  { partType :: MessagePartType
  , content :: String
  , language :: Maybe String
  , path :: Maybe String
  }

-- | Message time metadata
type MessageTime =
  { created :: Number
  , completed :: Maybe Number
  }

-- | Token usage information
type TokenUsage =
  { input :: Int
  , output :: Int
  , reasoning :: Int
  , cache :: CacheUsage
  }

-- | Cache usage
type CacheUsage =
  { read :: Int
  , write :: Int
  }

-- | Assistant metadata
type AssistantMetadata =
  { system :: Array String
  , modelID :: String
  , providerID :: String
  , path :: PathInfo
  , cost :: Number
  , summary :: Maybe Boolean
  , tokens :: TokenUsage
  }

-- | Path information
type PathInfo =
  { cwd :: String
  , root :: String
  }

-- | Tool execution metadata
type ToolMetadata =
  { title :: String
  , snapshot :: Maybe String
  , time :: ToolTime
  }

-- | Tool execution time
type ToolTime =
  { start :: Number
  , end :: Number
  }

-- | Error types
data MessageError = AuthError String | UnknownError String | OutputLengthError String

derive instance genericMessageError :: Generic MessageError _
derive instance eqMessageError :: Eq MessageError

instance showMessageError :: Show MessageError where
  show = genericShow

-- | Message metadata
type MessageMetadata =
  { time :: MessageTime
  , error :: Maybe MessageError
  , sessionID :: String
  , tool :: Maybe (Object ToolMetadata)
  , assistant :: Maybe AssistantMetadata
  , snapshot :: Maybe String
  }

-- | Message information
type MessageInfo =
  { id :: String
  , role :: MessageRole
  , parts :: Array MessagePart
  , metadata :: MessageMetadata
  }

instance encodeJsonMessageInfo :: EncodeJson MessageInfo where
  encodeJson m = encodeJson
    { id: m.id
    , role: m.role
    , parts: m.parts
    , metadata: m.metadata
    }

instance decodeJsonMessageInfo :: DecodeJson MessageInfo where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    role <- obj .: "role"
    parts <- obj .: "parts"
    metadata <- obj .: "metadata"
    pure { id, role, parts, metadata }
