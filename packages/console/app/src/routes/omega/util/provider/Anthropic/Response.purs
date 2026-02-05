-- | Anthropic Response Conversion
module Console.App.Routes.Omega.Util.Provider.Anthropic.Response
  ( fromAnthropicResponse
  , toAnthropicResponse
  ) where

import Prelude
import Console.App.Routes.Omega.Util.Provider.Provider (CommonResponse)

fromAnthropicResponse :: String -> CommonResponse
fromAnthropicResponse respJson = fromAnthropicResponseImpl respJson

foreign import fromAnthropicResponseImpl :: String -> CommonResponse

toAnthropicResponse :: CommonResponse -> String
toAnthropicResponse resp = toAnthropicResponseImpl resp

foreign import toAnthropicResponseImpl :: CommonResponse -> String
