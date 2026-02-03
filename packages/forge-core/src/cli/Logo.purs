-- | CLI Logo display
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/logo.ts
module Forge.CLI.Logo where

import Prelude
import Effect (Effect)
import Forge.Util.NotImplemented (notImplemented)

-- | Print the Forge logo
printLogo :: Effect Unit
printLogo = notImplemented "CLI.Logo.printLogo"

-- | Get the ASCII logo as a string
getLogo :: String
getLogo = """
   ____                   ______          __   
  / __ \____  ___  ____  / ____/___  ____/ /__ 
 / / / / __ \/ _ \/ __ \/ /   / __ \/ __  / _ \
/ /_/ / /_/ /  __/ / / / /___/ /_/ / /_/ /  __/
\____/ .___/\___/_/ /_/\____/\____/\__,_/\___/ 
    /_/                                        
"""
