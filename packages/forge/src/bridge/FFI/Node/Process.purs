-- | Bridge FFI for Node.js Process module
module Forge.Bridge.FFI.Node.Process where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)

-- | Get an environment variable
foreign import getEnv :: String -> Effect (Maybe String)

-- | Set an environment variable
foreign import setEnv :: String -> String -> Effect Unit

-- | Get current working directory
foreign import cwd :: Effect String

-- | Get process platform
foreign import platform :: String
