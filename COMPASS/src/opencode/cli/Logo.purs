-- | CLI Logo display
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/logo.ts
module Opencode.CLI.Logo where

import Prelude
import Effect (Effect)
import Opencode.Util.NotImplemented (notImplemented)

-- | Print the OpenCode logo
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
