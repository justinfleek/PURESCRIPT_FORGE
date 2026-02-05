-- | Omega V1 Chat Completions Route Handler
-- |
-- | Handles OpenAI-compatible chat completions requests.
-- | Wraps the main omega handler with OpenAI format.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/v1/chat/completions.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.V1.ChatCompletions
  ( handleChatCompletionsPOST
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Data.Array (find)
import Data.String as String
import Console.App.FFI.SolidStart (APIEvent, Response)
import Console.App.Routes.Omega.Util.Handler.Main (HandlerOptions, handleOmegaRequest, RequestHeaders, RequestBody)

-- | Handler options for OpenAI-compatible format
-- | Pure PureScript types - no Foreign
handlerOptions :: HandlerOptions
handlerOptions =
  { format: "oa-compat"
  , parseApiKey: \headers -> extractBearerTokenFromHeaders headers
  , parseModel: \_url body -> getBodyModel body
  , parseIsStream: \_url body -> getBodyStream body
  }

-- | Extract bearer token from Authorization header (pure PureScript)
extractBearerTokenFromHeaders :: RequestHeaders -> Maybe String
extractBearerTokenFromHeaders headers =
  case find (\h -> String.toLower h.key == "authorization") headers of
    Just h -> extractBearerToken h.value
    Nothing -> Nothing

-- | Extract bearer token from "Bearer <token>" string (pure PureScript)
extractBearerToken :: String -> Maybe String
extractBearerToken authHeader =
  case String.split (String.Pattern " ") authHeader of
    ["Bearer", token] -> Just token
    _ -> Nothing

-- | Get model from request body (pure PureScript - parses JSON string)
getBodyModel :: RequestBody -> String
getBodyModel body = parseJsonField body "model"

-- | Get stream flag from request body (pure PureScript - parses JSON string)
getBodyStream :: RequestBody -> Boolean
getBodyStream body = parseJsonField body "stream" == "true"

-- | Parse JSON field from request body (FFI boundary - JSON parsing)
foreign import parseJsonField :: RequestBody -> String -> String

-- | Handle POST request for chat completions
handleChatCompletionsPOST :: APIEvent -> Aff Response
handleChatCompletionsPOST event = handleOmegaRequest event handlerOptions
