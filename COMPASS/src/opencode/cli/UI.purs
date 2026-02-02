-- | CLI UI utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/ui.ts
module Opencode.CLI.UI where

import Prelude
import Effect (Effect)
import Opencode.Util.NotImplemented (notImplemented)

-- | Text styles for terminal output
type Style = String

-- | Common styles
textNormal :: Style
textNormal = "\x1b[0m"

textBold :: Style
textBold = "\x1b[1m"

textDim :: Style
textDim = "\x1b[2m"

textSuccess :: Style
textSuccess = "\x1b[32m"

textWarning :: Style
textWarning = "\x1b[33m"

textDanger :: Style
textDanger = "\x1b[31m"

textInfo :: Style
textInfo = "\x1b[36m"

textHighlight :: Style
textHighlight = "\x1b[35m"

-- | Print a line with styles
println :: Array String -> Effect Unit
println parts = notImplemented "CLI.UI.println"

-- | Print an error message
error :: String -> Effect Unit
error msg = notImplemented "CLI.UI.error"

-- | Format markdown for terminal display
markdown :: String -> String
markdown input = input -- TODO: Implement markdown rendering

-- | Clear the screen
clearScreen :: Effect Unit
clearScreen = notImplemented "CLI.UI.clearScreen"
