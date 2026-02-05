-- | Omega V1 Messages Route Handler
-- |
-- | Handles Anthropic-compatible messages requests.
-- | Wraps the main omega handler with Anthropic format.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/v1/messages.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.V1.Messages
  ( handleMessagesPOST
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Data.Array (find)
import Data.String as String
import Console.App.FFI.SolidStart (APIEvent, Response)
import Console.App.Routes.Omega.Util.Handler.Main (HandlerOptions, handleOmegaRequest, RequestHeaders, RequestBody)

-- | Handler options for Anthropic format
-- | Pure PureScript types - no Foreign
handlerOptions :: HandlerOptions
handlerOptions =
  { format: "anthropic"
  , parseApiKey: \headers -> findHeader headers "x-api-key"
  , parseModel: \_url body -> getBodyModel body
  , parseIsStream: \_url body -> getBodyStream body
  }

-- | Find header value (pure PureScript)
findHeader :: RequestHeaders -> String -> Maybe String
findHeader headers key =
  case find (\h -> String.toLower h.key == String.toLower key) headers of
    Just h -> Just h.value
    Nothing -> Nothing

-- | Get model from request body (pure PureScript - parses JSON string)
getBodyModel :: RequestBody -> String
getBodyModel body = parseJsonField body "model"

-- | Get stream flag from request body (pure PureScript - parses JSON string)
getBodyStream :: RequestBody -> Boolean
getBodyStream body = parseJsonField body "stream" == "true"

-- | Parse JSON field from request body (FFI boundary - JSON parsing)
foreign import parseJsonField :: RequestBody -> String -> String

-- | Handle POST request for messages
handleMessagesPOST :: APIEvent -> Aff Response
handleMessagesPOST event = handleOmegaRequest event handlerOptions
