{-|
Module      : Sidepanel.Components.ErrorAnalysis.StackTraceParser
Description : Parse and analyze stack traces
Parses stack traces from various languages and formats.
-}
module Sidepanel.Components.ErrorAnalysis.StackTraceParser where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Sidepanel.Components.ErrorAnalysis.ErrorAnalysisTypes
  ( StackTrace
  , StackFrame
  )

-- | Parse stack trace from raw string
parseStackTrace :: String -> StackTrace
parseStackTrace raw =
  { frames: parseFrames raw
  , raw: raw
  }

-- | Parse stack frames from trace
parseFrames :: String -> Array StackFrame
parseFrames raw =
  let lines = String.split (String.Pattern "\n") raw
      -- Filter out empty lines and headers
      frameLines = Array.filter (\l -> 
        String.length l > 0 &&
        not (String.contains (String.Pattern "Error:") l) &&
        not (String.contains (String.Pattern "at Object.") l)
      ) lines
  in
    Array.mapMaybe parseFrame frameLines

-- | Parse single stack frame
parseFrame :: String -> Maybe StackFrame
parseFrame line =
  -- Try different formats
  case parseNodeFrame line of
    Just frame -> Just frame
    Nothing -> case parsePureScriptFrame line of
      Just frame -> Just frame
      Nothing -> case parseHaskellFrame line of
        Just frame -> Just frame
        Nothing -> case parseGenericFrame line of
          Just frame -> Just frame
          Nothing -> Nothing

-- | Parse Node.js/JavaScript stack frame
-- Format: "    at functionName (file:line:column)"
-- Format: "    at file:line:column"
parseNodeFrame :: String -> Maybe StackFrame
parseNodeFrame line =
  let trimmed = String.trim line
  in
    if String.contains (String.Pattern "at ") trimmed then
      let withoutAt = String.drop 3 trimmed
          parts = String.split (String.Pattern " ") withoutAt
          function = case Array.index parts 0 of
            Nothing -> Nothing
            Just fn -> if fn == "" then Nothing else Just fn
          
          locationPart = case Array.index parts 1 of
            Nothing -> withoutAt
            Just loc -> loc
          
          location = parseLocation locationPart
      in
        Just
          { function: function
          , file: location.file
          , line: location.line
          , column: location.column
          , code: Nothing
          }
    else
      Nothing

-- | Parse PureScript stack frame
-- Format: "Error at Module.Function (file:line:column)"
parsePureScriptFrame :: String -> Maybe StackFrame
parsePureScriptFrame line =
  let trimmed = String.trim line
  in
    if String.contains (String.Pattern " at ") trimmed then
      let parts = String.split (String.Pattern " at ") trimmed
          functionPart = case Array.index parts 1 of
            Nothing -> ""
            Just fp -> fp
          
          functionAndLocation = String.split (String.Pattern " (") functionPart
          function = case Array.index functionAndLocation 0 of
            Nothing -> Nothing
            Just fn -> if fn == "" then Nothing else Just fn
          
          locationStr = case Array.index functionAndLocation 1 of
            Nothing -> ""
            Just loc -> String.dropRight 1 loc  -- Remove closing paren
          
          location = parseLocation locationStr
      in
        Just
          { function: function
          , file: location.file
          , line: location.line
          , column: location.column
          , code: Nothing
          }
    else
      Nothing

-- | Parse Haskell stack frame
-- Format: "Module.function (file:line:column)"
parseHaskellFrame :: String -> Maybe StackFrame
parseHaskellFrame line =
  let trimmed = String.trim line
  in
    if String.contains (String.Pattern " (") trimmed then
      let parts = String.split (String.Pattern " (") trimmed
          function = case Array.index parts 0 of
            Nothing -> Nothing
            Just fn -> if fn == "" then Nothing else Just fn
          
          locationStr = case Array.index parts 1 of
            Nothing -> ""
            Just loc -> String.dropRight 1 loc  -- Remove closing paren
          
          location = parseLocation locationStr
      in
        Just
          { function: function
          , file: location.file
          , line: location.line
          , column: location.column
          , code: Nothing
          }
    else
      Nothing

-- | Parse generic frame format
-- Format: "file:line:column"
parseGenericFrame :: String -> Maybe StackFrame
parseGenericFrame line =
  let trimmed = String.trim line
      location = parseLocation trimmed
  in
    if location.file /= Nothing || location.line /= Nothing then
      Just
        { function: Nothing
        , file: location.file
        , line: location.line
        , column: location.column
        , code: Nothing
        }
    else
      Nothing

-- | Parse location from string (file:line:column)
parseLocation :: String -> { file :: Maybe String, line :: Maybe Int, column :: Maybe Int }
parseLocation str =
  let parts = String.split (String.Pattern ":") str
      file = case Array.index parts 0 of
        Nothing -> Nothing
        Just f -> if f == "" then Nothing else Just f
      
      line = case Array.index parts 1 of
        Nothing -> Nothing
        Just l -> case parseInt l of
          Nothing -> Nothing
          Just n -> Just n
      
      column = case Array.index parts 2 of
        Nothing -> Nothing
        Just c -> case parseInt c of
          Nothing -> Nothing
          Just n -> Just n
  in
    { file: file, line: line, column: column }

-- | Parse integer from string
parseInt :: String -> Maybe Int
parseInt str =
  let trimmed = String.trim str
      -- Remove non-numeric prefix/suffix but keep negative sign
      cleaned = if String.take 1 trimmed == "-" then
            "-" <> String.dropWhile (\c -> c < "0" || c > "9") (String.drop 1 trimmed)
          else
            String.dropWhile (\c -> c < "0" || c > "9") trimmed
      
      -- Extract numeric part
      numericPart = String.takeWhile (\c -> (c >= "0" && c <= "9") || c == "-") cleaned
      
      -- Parse using JavaScript parseInt via FFI
      parsed = parseIntFFI numericPart
  in
    if parsed == 0 && numericPart /= "0" && String.length numericPart > 0 then
      Nothing  -- Failed to parse
    else
      Just parsed

-- | FFI for integer parsing
foreign import parseIntFFI :: String -> Int
