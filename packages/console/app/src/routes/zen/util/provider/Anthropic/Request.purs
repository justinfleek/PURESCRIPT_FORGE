-- | Anthropic Request Conversion
-- | Converts between Anthropic format and CommonRequest
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/provider/anthropic.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Provider.Anthropic.Request
  ( fromAnthropicRequest
  , toAnthropicRequest
  ) where

import Prelude
import Console.App.Routes.Omega.Util.Provider.Provider (CommonRequest)

-- | Convert Anthropic request format to CommonRequest
fromAnthropicRequest :: String -> CommonRequest
fromAnthropicRequest bodyJson = fromAnthropicRequestImpl bodyJson

foreign import fromAnthropicRequestImpl :: String -> CommonRequest

-- | Convert CommonRequest to Anthropic request format
toAnthropicRequest :: CommonRequest -> String
toAnthropicRequest req = toAnthropicRequestImpl req

foreign import toAnthropicRequestImpl :: CommonRequest -> String
