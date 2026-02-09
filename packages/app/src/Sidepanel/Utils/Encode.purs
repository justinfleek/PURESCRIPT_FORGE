-- | Base64 encoding utility for URL-safe path encoding
module Sidepanel.Utils.Encode
  ( base64Encode
  ) where

import Prelude

-- | Encode a string to base64 for use in URL paths.
-- | Uses the browser's btoa() function under the hood via FFI.
foreign import base64Encode :: String -> String
