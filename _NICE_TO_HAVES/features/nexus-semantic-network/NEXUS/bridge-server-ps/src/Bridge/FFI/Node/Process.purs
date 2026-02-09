-- | Node.js Process FFI bindings
module Bridge.FFI.Node.Process where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)

-- | Get environment variable
foreign import getEnv :: String -> Effect (Maybe String)
