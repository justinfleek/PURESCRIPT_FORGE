-- | OpenAI Request Conversion
-- | Converts between OpenAI format and CommonRequest
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/openai.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Provider.OpenAI.Request
  ( fromOpenaiRequest
  , toOpenaiRequest
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Console.App.Routes.Omega.Util.Provider.Provider (CommonRequest, CommonMessage, ToolChoice(..))

-- | Convert OpenAI request format to CommonRequest
-- | FFI handles all complex conversion logic
fromOpenaiRequest :: String -> CommonRequest
fromOpenaiRequest bodyJson = fromOpenaiRequestImpl bodyJson

foreign import fromOpenaiRequestImpl :: String -> CommonRequest

-- | Convert CommonRequest to OpenAI request format
-- | FFI handles all complex conversion logic
toOpenaiRequest :: CommonRequest -> String
toOpenaiRequest req = toOpenaiRequestImpl req

foreign import toOpenaiRequestImpl :: CommonRequest -> String


-- | Helper: fromMaybe
fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe default Nothing = default
fromMaybe _ (Just x) = x

-- | Helper: orElse
orElse :: forall a. Maybe a -> Maybe a -> Maybe a
orElse (Just x) _ = Just x
orElse Nothing y = y
