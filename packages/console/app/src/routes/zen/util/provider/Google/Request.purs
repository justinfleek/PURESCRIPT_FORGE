-- | Google Request Conversion
module Console.App.Routes.Omega.Util.Provider.Google.Request
  ( fromGoogleRequest
  , toGoogleRequest
  ) where

import Prelude
import Console.App.Routes.Omega.Util.Provider.Provider (CommonRequest)

fromGoogleRequest :: String -> CommonRequest
fromGoogleRequest bodyJson = fromGoogleRequestImpl bodyJson

foreign import fromGoogleRequestImpl :: String -> CommonRequest

toGoogleRequest :: CommonRequest -> String
toGoogleRequest req = toGoogleRequestImpl req

foreign import toGoogleRequestImpl :: CommonRequest -> String
