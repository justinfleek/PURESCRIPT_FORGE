{-|
Module      : Forge.CLI.UI
Description : CLI UI utilities

Terminal output utilities with styling, colors, and formatting support.
-}
module Forge.CLI.UI
  ( -- * Styles
    Style
  , textNormal
  , textBold
  , textDim
  , textItalic
  , textUnderline
  , textSuccess
  , textWarning
  , textDanger
  , textInfo
  , textHighlight
  , textMuted
    -- * Output
  , println
  , print
  , error
  , warn
  , info
  , success
    -- * Screen Control
  , clearScreen
  , clearLine
  , moveCursor
    -- * Formatting
  , styled
  , markdown
  , table
  , progressBar
    -- * Input
  , prompt
  , confirm
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect (Effect)
import Effect.Aff (Aff)

-- ============================================================================
-- FFI
-- ============================================================================

foreign import printlnFFI :: String -> Effect Unit
foreign import printFFI :: String -> Effect Unit
foreign import printErrorFFI :: String -> Effect Unit
foreign import clearScreenFFI :: Effect Unit
foreign import clearLineFFI :: Effect Unit
foreign import moveCursorFFI :: Int -> Int -> Effect Unit
foreign import promptFFI :: String -> Aff String

-- ============================================================================
-- STYLES (ANSI Escape Codes)
-- ============================================================================

-- | Style type alias
type Style = String

-- | Reset all styles
textNormal :: Style
textNormal = "\x1b[0m"

-- | Bold text
textBold :: Style
textBold = "\x1b[1m"

-- | Dim/faint text
textDim :: Style
textDim = "\x1b[2m"

-- | Italic text
textItalic :: Style
textItalic = "\x1b[3m"

-- | Underlined text
textUnderline :: Style
textUnderline = "\x1b[4m"

-- | Green (success)
textSuccess :: Style
textSuccess = "\x1b[32m"

-- | Yellow (warning)
textWarning :: Style
textWarning = "\x1b[33m"

-- | Red (danger/error)
textDanger :: Style
textDanger = "\x1b[31m"

-- | Cyan (info)
textInfo :: Style
textInfo = "\x1b[36m"

-- | Magenta (highlight)
textHighlight :: Style
textHighlight = "\x1b[35m"

-- | Gray (muted)
textMuted :: Style
textMuted = "\x1b[90m"

-- ============================================================================
-- OUTPUT
-- ============================================================================

-- | Print a line with parts concatenated
println :: Array String -> Effect Unit
println parts = printlnFFI (String.joinWith "" parts)

-- | Print without newline
print :: Array String -> Effect Unit
print parts = printFFI (String.joinWith "" parts)

-- | Print an error message (red, to stderr)
error :: String -> Effect Unit
error msg = printErrorFFI (textDanger <> "Error: " <> textNormal <> msg)

-- | Print a warning message (yellow)
warn :: String -> Effect Unit
warn msg = printlnFFI (textWarning <> "Warning: " <> textNormal <> msg)

-- | Print an info message (cyan)
info :: String -> Effect Unit
info msg = printlnFFI (textInfo <> "Info: " <> textNormal <> msg)

-- | Print a success message (green)
success :: String -> Effect Unit
success msg = printlnFFI (textSuccess <> "✓ " <> textNormal <> msg)

-- ============================================================================
-- SCREEN CONTROL
-- ============================================================================

-- | Clear the entire screen
clearScreen :: Effect Unit
clearScreen = clearScreenFFI

-- | Clear the current line
clearLine :: Effect Unit
clearLine = clearLineFFI

-- | Move cursor to position (row, col)
moveCursor :: Int -> Int -> Effect Unit
moveCursor = moveCursorFFI

-- ============================================================================
-- FORMATTING
-- ============================================================================

-- | Apply a style to text
styled :: Style -> String -> String
styled style text = style <> text <> textNormal

-- | Basic markdown rendering for terminal
-- | Handles: **bold**, *italic*, `code`, headers
markdown :: String -> String
markdown input =
  input
    # replaceBold
    # replaceItalic
    # replaceCode
    # replaceHeaders

replaceBold :: String -> String
replaceBold s = 
  let parts = String.split (String.Pattern "**") s
  in formatPairs textBold parts

replaceItalic :: String -> String
replaceItalic s =
  let parts = String.split (String.Pattern "*") s
  in formatPairs textItalic parts

replaceCode :: String -> String
replaceCode s =
  let parts = String.split (String.Pattern "`") s
  in formatPairs textDim parts

formatPairs :: Style -> Array String -> String
formatPairs style parts =
  Array.mapWithIndex (\idx part -> 
    if idx `mod` 2 == 1 
    then style <> part <> textNormal
    else part
  ) parts # String.joinWith ""

replaceHeaders :: String -> String
replaceHeaders s =
  s # String.split (String.Pattern "\n")
    # map formatHeader
    # String.joinWith "\n"
  where
    formatHeader line
      | String.take 4 line == "### " = 
          textBold <> String.drop 4 line <> textNormal
      | String.take 3 line == "## " = 
          textBold <> textHighlight <> String.drop 3 line <> textNormal
      | String.take 2 line == "# " = 
          textBold <> textInfo <> String.drop 2 line <> textNormal
      | otherwise = line

-- | Render a simple table
table :: Array (Array String) -> String
table rows =
  let widths = calculateWidths rows
      formatted = map (formatRow widths) rows
  in String.joinWith "\n" formatted
  where
    calculateWidths :: Array (Array String) -> Array Int
    calculateWidths rs =
      let maxCols = Array.foldl (\acc row -> max acc (Array.length row)) 0 rs
      in Array.range 0 (maxCols - 1) # Array.map (\col ->
           Array.foldl (\acc row -> 
             case Array.index row col of
               Nothing -> acc
               Just cell -> max acc (String.length cell)
           ) 0 rs
         )
    
    formatRow :: Array Int -> Array String -> String
    formatRow widths cells =
      Array.mapWithIndex (\idx cell ->
        let width = Array.index widths idx # fromMaybe 0
        in padRight width cell
      ) cells # String.joinWith " | "
    
    padRight :: Int -> String -> String
    padRight width str =
      str <> fromCharArrayImpl (Array.replicate (width - String.length str) ' ')
    
    fromCharArrayImpl :: Array Char -> String
    fromCharArrayImpl = fromCharArrayFFI

foreign import fromCharArrayFFI :: Array Char -> String
    
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe def Nothing = def
    fromMaybe _ (Just x) = x

-- | Render a progress bar
progressBar :: Int -> Int -> Int -> String
progressBar width current total =
  let ratio = if total > 0 then toNumber current / toNumber total else 0.0
      filled = floor (ratio * toNumber width)
      empty = width - filled
      bar = fromCharArrayFFI (Array.replicate filled '█') <>
            fromCharArrayFFI (Array.replicate empty '░')
      percent = show (floor (ratio * 100.0)) <> "%"
  in "[" <> bar <> "] " <> percent

-- ============================================================================
-- INPUT
-- ============================================================================

-- | Prompt for input
prompt :: String -> Aff String
prompt = promptFFI

-- | Prompt for yes/no confirmation
confirm :: String -> Aff Boolean
confirm message = do
  response <- prompt (message <> " (y/n): ")
  pure $ String.toLower (String.trim response) `Array.elem` ["y", "yes"]

-- ============================================================================
-- HELPERS
-- ============================================================================

toNumber :: Int -> Number
toNumber = toNumberFFI

floor :: Number -> Int
floor = floorFFI

foreign import toNumberFFI :: Int -> Number
foreign import floorFFI :: Number -> Int
