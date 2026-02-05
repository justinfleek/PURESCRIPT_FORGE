-- | Google Response Conversion
module Console.App.Routes.Omega.Util.Provider.Google.Response
  ( fromGoogleResponse
  , toGoogleResponse
  ) where

import Prelude
import Console.App.Routes.Omega.Util.Provider.Provider (CommonResponse)

fromGoogleResponse :: String -> CommonResponse
fromGoogleResponse respJson = fromGoogleResponseImpl respJson

foreign import fromGoogleResponseImpl :: String -> CommonResponse

toGoogleResponse :: CommonResponse -> String
toGoogleResponse resp = toGoogleResponseImpl resp

foreign import toGoogleResponseImpl :: CommonResponse -> String
