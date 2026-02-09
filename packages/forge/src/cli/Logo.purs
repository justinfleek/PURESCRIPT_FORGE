{-|
Module      : Forge.CLI.Logo
Description : CLI Logo display

ASCII art logo for the Forge CLI.
-}
module Forge.CLI.Logo
  ( -- * Logo Display
    printLogo
  , printLogoColored
    -- * Logo Data
  , getLogo
  , getLogoColored
  , getVersion
  ) where

import Prelude

import Effect (Effect)

-- ============================================================================
-- FFI
-- ============================================================================

-- | Print to console
foreign import printlnFFI :: String -> Effect Unit

-- ============================================================================
-- LOGO DISPLAY
-- ============================================================================

-- | Print the Forge logo to console
printLogo :: Effect Unit
printLogo = printlnFFI getLogo

-- | Print the logo with ANSI colors
printLogoColored :: Effect Unit
printLogoColored = printlnFFI getLogoColored

-- ============================================================================
-- LOGO DATA
-- ============================================================================

-- | Get the ASCII logo as a string
getLogo :: String
getLogo = """
  ______                    
 |  ____|                   
 | |__ ___  _ __ __ _  ___ 
 |  __/ _ \| '__/ _` |/ _ \
 | | | (_) | | | (_| |  __/
 |_|  \___/|_|  \__, |\___|
                 __/ |      
                |___/       
"""

-- | Get the colored logo (ANSI escape codes)
getLogoColored :: String
getLogoColored = 
  "\x1b[36m" <>  -- Cyan color
  """
  ______                    
 |  ____|                   
 | |__ ___  _ __ __ _  ___ 
 |  __/ _ \| '__/ _` |/ _ \
 | | | (_) | | | (_| |  __/
 |_|  \___/|_|  \__, |\___|
                 __/ |      
                |___/       
""" <>
  "\x1b[0m"  -- Reset color

-- | Get the version string
getVersion :: String
getVersion = "0.1.0"
