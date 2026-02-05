-- | OpenAI-Compatible Request Conversion
module Console.App.Routes.Omega.Util.Provider.OpenAICompatible.Request
  ( fromOaCompatibleRequest
  , toOaCompatibleRequest
  ) where

import Prelude
import Console.App.Routes.Omega.Util.Provider.Provider (CommonRequest)

fromOaCompatibleRequest :: String -> CommonRequest
fromOaCompatibleRequest bodyJson = fromOaCompatibleRequestImpl bodyJson

foreign import fromOaCompatibleRequestImpl :: String -> CommonRequest

toOaCompatibleRequest :: CommonRequest -> String
toOaCompatibleRequest req = toOaCompatibleRequestImpl req

foreign import toOaCompatibleRequestImpl :: CommonRequest -> String
