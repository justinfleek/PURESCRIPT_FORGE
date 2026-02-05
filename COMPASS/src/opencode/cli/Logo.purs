-- | CLI Logo display
module Opencode.CLI.Logo where

import Prelude
import Effect (Effect)
import Opencode.CLI.UI as UI

-- | Print the OpenCode logo
printLogo :: Effect Unit
printLogo = UI.println [getLogo]

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
