-- | Color utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/color.ts
module Forge.Util.Color where

import Prelude

-- | ANSI color codes
reset :: String
reset = "\x1b[0m"

red :: String
red = "\x1b[31m"

green :: String
green = "\x1b[32m"

yellow :: String
yellow = "\x1b[33m"

blue :: String
blue = "\x1b[34m"

magenta :: String
magenta = "\x1b[35m"

cyan :: String
cyan = "\x1b[36m"

white :: String
white = "\x1b[37m"

-- | Apply color to text
colorize :: String -> String -> String
colorize color text = color <> text <> reset
