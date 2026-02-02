-- | Fetch API FFI bindings
module Bridge.FFI.Node.Fetch where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)

-- | Opaque Response type
foreign import data Response :: Type

-- | Opaque Headers type
foreign import data Headers :: Type

-- | Request options
type RequestOptions =
  { method :: String
  , headers :: Array { key :: String, value :: String }
  , body :: Maybe String
  }

-- | Fetch request
foreign import fetch :: String -> RequestOptions -> Aff (Either String Response)

-- | Get response headers
foreign import getHeaders :: Response -> Effect Headers

-- | Get header value
foreign import getHeader :: Headers -> String -> Effect (Maybe String)

-- | Parse JSON response
foreign import json :: Response -> Aff (Either String String)

-- | Check if response is OK
foreign import ok :: Response -> Effect Boolean

-- | Get response status
foreign import status :: Response -> Effect Int
