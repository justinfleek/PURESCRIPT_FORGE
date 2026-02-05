-- | OpenAI-Compatible Response Conversion
module Console.App.Routes.Omega.Util.Provider.OpenAICompatible.Response
  ( fromOaCompatibleResponse
  , toOaCompatibleResponse
  ) where

import Prelude
import Console.App.Routes.Omega.Util.Provider.Provider (CommonResponse)

fromOaCompatibleResponse :: String -> CommonResponse
fromOaCompatibleResponse respJson = fromOaCompatibleResponseImpl respJson

foreign import fromOaCompatibleResponseImpl :: String -> CommonResponse

toOaCompatibleResponse :: CommonResponse -> String
toOaCompatibleResponse resp = toOaCompatibleResponseImpl resp

foreign import toOaCompatibleResponseImpl :: CommonResponse -> String
