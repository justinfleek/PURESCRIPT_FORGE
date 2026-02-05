-- | CLI UI utilities
module Opencode.CLI.UI where

import Prelude
import Effect (Effect)
import Effect.Console as Console
import Data.String as String
import Data.Array as Array

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
println parts = do
  let output = String.joinWith "" parts <> textNormal
  Console.log output

-- | Print an error message
error :: String -> Effect Unit
error msg = Console.error (textDanger <> msg <> textNormal)

-- | Format markdown for terminal display
-- | Basic markdown formatting: strips markdown syntax, preserves text
markdown :: String -> String
markdown input =
  let lines = String.split (String.Pattern "\n") input
      formatted = Array.map formatMarkdownLine lines
  in String.joinWith "\n" formatted
  where
    formatMarkdownLine :: String -> String
    formatMarkdownLine line =
      -- Remove markdown headers (# ## ###) - simple prefix removal
      let noHeaders = if String.startsWith (String.Pattern "#") line
            then String.dropWhile (\c -> c == '#' || c == ' ') line
            else line
      -- Remove bold markers (**text**)
      let noBold = String.replaceAll (String.Pattern "**") (String.Replacement "") noHeaders
      -- Remove italic markers (*text*)
      let noItalic = String.replaceAll (String.Pattern "*") (String.Replacement "") noBold
      -- Remove code blocks (`code`)
      let noCode = String.replaceAll (String.Pattern "`") (String.Replacement "") noItalic
      in noCode

-- | Clear the screen
clearScreen :: Effect Unit
clearScreen = clearTerminalScreen
  where
    foreign import clearTerminalScreen :: Effect Unit
