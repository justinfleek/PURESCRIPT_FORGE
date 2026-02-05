-- | Omega V1 Model Detail Route Handler
-- |
-- | Handles Google-compatible model detail requests.
-- | Wraps the main omega handler with Google format.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/v1/models/[model].ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.V1.ModelDetail
  ( handleModelDetailPOST
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Data.Array (find, length, unsafeIndex) as Array
import Data.String as String
import Console.App.FFI.SolidStart (APIEvent, Response)
import Console.App.Routes.Omega.Util.Handler.Main (HandlerOptions, handleOmegaRequest, RequestHeaders)

-- | Handler options for Google format
-- | Pure PureScript types - no Foreign
handlerOptions :: HandlerOptions
handlerOptions =
  { format: "google"
  , parseApiKey: \headers -> findHeader headers "x-goog-api-key"
  , parseModel: \url _body -> extractModelFromUrl url
  , parseIsStream: \url _body -> isStreamUrl url
  }

-- | Find header value (pure PureScript)
findHeader :: RequestHeaders -> String -> Maybe String
findHeader headers key =
  case Array.find (\h -> String.toLower h.key == String.toLower key) headers of
    Just h -> Just h.value
    Nothing -> Nothing

-- | Extract model ID from URL (pure PureScript)
-- | Format: /omega/v1/models/gemini-3-pro:streamGenerateContent?alt=sse
-- | Returns: gemini-3-pro
extractModelFromUrl :: String -> String
extractModelFromUrl url =
  let
    -- Remove query string
    path = case String.split (String.Pattern "?") url of
      [p, _] -> p
      _ -> url
    -- Split by / and get last part
    parts = String.split (String.Pattern "/") path
    lastPart = case Array.length parts of
      0 -> ""
      n -> case Array.unsafeIndex parts (n - 1) of
        Just p -> p
        Nothing -> ""
    -- Remove :streamGenerateContent suffix if present
    modelId = case String.split (String.Pattern ":") lastPart of
      [id, _] -> id
      _ -> lastPart
  in modelId


-- | Check if URL indicates streaming (pure PureScript)
-- | Checks if path ends with :streamGenerateContent
isStreamUrl :: String -> Boolean
isStreamUrl url = String.contains (String.Pattern ":streamGenerateContent") url

-- | Handle POST request for model detail
handleModelDetailPOST :: APIEvent -> Aff Response
handleModelDetailPOST event = handleOmegaRequest event handlerOptions
