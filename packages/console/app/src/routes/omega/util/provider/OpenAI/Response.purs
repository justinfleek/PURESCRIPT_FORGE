-- | OpenAI Response Conversion
-- | Converts between OpenAI format and CommonResponse
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Provider.OpenAI.Response
  ( fromOpenaiResponse
  , toOpenaiResponse
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Console.App.Routes.Omega.Util.Provider.Provider (CommonResponse, FinishReason(..))

-- | Convert OpenAI response format to CommonResponse
fromOpenaiResponse :: String -> CommonResponse
fromOpenaiResponse respJson = fromOpenaiResponseImpl respJson

foreign import fromOpenaiResponseImpl :: String -> CommonResponse

-- | Convert CommonResponse to OpenAI response format
toOpenaiResponse :: CommonResponse -> String
toOpenaiResponse resp = toOpenaiResponseImpl resp

foreign import toOpenaiResponseImpl :: CommonResponse -> String
