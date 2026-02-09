-- | Node.js process FFI
module Bridge.FFI.Node.Process where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)
import Data.DateTime (DateTime)

-- | Get environment variable
foreign import getEnv :: String -> Effect (Maybe String)

-- | Generate session ID
foreign import generateSessionId :: Effect String

-- | Parse datetime string
foreign import parseDateTime :: String -> Effect DateTime
