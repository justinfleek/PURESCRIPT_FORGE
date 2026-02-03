-- | Pino logger FFI bindings
module Bridge.FFI.Node.Pino where

import Prelude
import Effect (Effect)

-- | Opaque Logger type
foreign import data Logger :: Type

-- | Logger options
type LoggerOptions =
  { name :: String
  , level :: String
  }

-- | Create logger
foreign import create :: LoggerOptions -> Effect Logger

-- | Log info
foreign import info :: Logger -> String -> Effect Unit

-- | Log info with fields
foreign import infoFields :: Logger -> String -> String -> Effect Unit

-- | Log warn
foreign import warn :: Logger -> String -> Effect Unit

-- | Log warn with fields
foreign import warnFields :: Logger -> String -> String -> Effect Unit

-- | Log error
foreign import error :: Logger -> String -> Effect Unit

-- | Log error with fields
foreign import errorFields :: Logger -> String -> String -> Effect Unit

-- | Log debug
foreign import debug :: Logger -> String -> Effect Unit

-- | Log debug with fields
foreign import debugFields :: Logger -> String -> String -> Effect Unit
