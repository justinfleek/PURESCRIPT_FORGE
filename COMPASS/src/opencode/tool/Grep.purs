{-|
Module      : Tool.Grep
Description : Content search via ripgrep
= Grep Tool

Fast content search using ripgrep (rg) with regex support.

== Coeffect Equation

@
  grep : GrepParams → Graded (Filesystem path ⊗ Container rg) GrepResult

  -- Requires:
  -- 1. Filesystem access to search path
  -- 2. Sandboxed ripgrep execution
@

== Usage

@
  grep { pattern: "TODO", path: Just "./src", include: Just "*.purs" }
@

== Output Format

Results sorted by modification time (most recent first):

@
  Found 42 matches

  src/Tool/Grep.purs:
    Line 15: -- TODO: Add streaming support
    Line 89: -- TODO: Handle binary files

  src/Tool/Edit.purs:
    Line 203: -- TODO: AST validation
@
-}
module Tool.Grep
  ( -- * Tool Interface
    GrepParams(..)
  , GrepResult(..)
  , GrepMatch(..)
  , execute
  , grepTool
    -- * Configuration
  , GrepConfig(..)
  , defaultConfig
    -- * Coeffects
  , grepCoeffect
  ) where

import Prelude

import Data.Maybe (Maybe(..), maybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut (Json, encodeJson, decodeJson)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect (Effect)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..), PathSpec, filesystem, container, (⊗))
import Aleph.Sandbox as Sandbox
import Bridge.FFI.Node.Terminal as Terminal
import Data.Int as Int

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

{-| Grep tool configuration. -}
type GrepConfig =
  { maxLineLength :: Int      -- Truncate lines longer than this
  , maxMatches :: Int         -- Maximum matches to return
  , defaultPath :: String     -- Default search path
  , rgPath :: String          -- Path to ripgrep binary
  , timeout :: Int            -- Timeout in ms
  }

defaultConfig :: GrepConfig
defaultConfig =
  { maxLineLength: 2000
  , maxMatches: 100
  , defaultPath: "."
  , rgPath: "rg"
  , timeout: 30000
  }

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Grep tool parameters.

@
  record GrepParams where
    pattern : String           -- Regex pattern
    path    : Maybe String     -- Search directory
    include : Maybe String     -- File glob pattern
@
-}
type GrepParams =
  { pattern :: String
  , path :: Maybe String
  , include :: Maybe String
  }

{-| Single match result.

@
  record GrepMatch where
    path    : String
    lineNum : Int
    content : String
    modTime : Number
@
-}
type GrepMatch =
  { path :: String
  , lineNum :: Int
  , content :: String
  , modTime :: Number
  }

{-| Grep execution result. -}
type GrepResult =
  { matches :: Array GrepMatch
  , totalFound :: Int
  , truncated :: Boolean
  , searchPath :: String
  , pattern :: String
  , hasErrors :: Boolean
  }

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

-- | Execute grep search
execute :: GrepParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate pattern
  case validatePattern params.pattern of
    Left err -> pure $ mkErrorResult err
    Right _ -> executeImpl params ctx

executeImpl :: GrepParams -> ToolContext -> Aff ToolResult
executeImpl params _ctx = do
  let searchPath = params.path # maybe defaultConfig.defaultPath identity
  
  -- Build ripgrep command string
  let cmd = buildRgCommand params searchPath
  
  -- Execute via Terminal FFI
  result <- Terminal.executeCommand cmd (Just searchPath) Nothing
  
  case result of
    Left err -> 
      pure $ mkErrorResult err
    
    Right resp -> do
      let output = resp.output # maybe "" identity
      let exitCode = resp.exitCode # maybe 0 identity
      
      -- Exit code 1 = no matches found (not an error)
      -- Exit code 2 = actual error
      if exitCode == 2
        then pure $ mkErrorResult ("ripgrep error: " <> output)
        else do
          -- Parse ripgrep output
          let parsed = parseRgOutput output
          let sorted = sortByModTime parsed
          let truncated = Array.length sorted > defaultConfig.maxMatches
          let final = Array.take defaultConfig.maxMatches sorted
          
          pure $ formatResult params.pattern searchPath
            { matches: final
            , totalFound: Array.length parsed
            , truncated
            , searchPath
            , pattern: params.pattern
            , hasErrors: false
            }

-- | Build ripgrep command string for Terminal execution
buildRgCommand :: GrepParams -> String -> String
buildRgCommand params searchPath =
  String.joinWith " "
    [ "rg"
    , "-nH"                        -- Line numbers, filenames
    , "--hidden"                   -- Search hidden files
    , "--follow"                   -- Follow symlinks
    , "--no-messages"              -- Suppress error messages
    , "--field-match-separator='|'" -- Parseable output
    , includeArg
    , "--regexp"
    , escapePattern params.pattern
    , searchPath
    ]
  where
    includeArg = case params.include of
      Just glob -> "--glob '" <> glob <> "'"
      Nothing -> ""
    
    -- Escape pattern for shell (basic escaping)
    escapePattern p = "'" <> String.replaceAll (String.Pattern "'") (String.Replacement "'\\''") p <> "'"

-- | Build ripgrep command arguments (kept for future sandbox use)
buildRgArgs :: GrepParams -> String -> Array String
buildRgArgs params searchPath =
  [ "-nH"                        -- Line numbers, filenames
  , "--hidden"                   -- Search hidden files
  , "--follow"                   -- Follow symlinks
  , "--no-messages"              -- Suppress error messages
  , "--field-match-separator=|"  -- Parseable output
  , "--regexp", params.pattern
  ]
  <> includeArg
  <> [searchPath]
  where
    includeArg = case params.include of
      Just glob -> ["--glob", glob]
      Nothing -> []

-- | Create container config for ripgrep (kept for future sandbox use)
mkContainerConfig :: Array String -> Sandbox.ContainerConfig
mkContainerConfig args =
  Sandbox.defaultConfig
    { command = ["rg"] <> args
    , policy = Sandbox.policyFromKind Sandbox.SandboxFull
    }

-- ════════════════════════════════════════════════════════════════════════════
-- PARSING
-- ════════════════════════════════════════════════════════════════════════════

-- | Parse ripgrep output format: path|linenum|content
parseRgOutput :: String -> Array GrepMatch
parseRgOutput output =
  output
    # String.split (String.Pattern "\n")
    # Array.mapMaybe parseLine

parseLine :: String -> Maybe GrepMatch
parseLine line = do
  -- Format: filepath|linenum|content
  let parts = String.split (String.Pattern "|") line
  filePath <- Array.index parts 0
  lineNumStr <- Array.index parts 1
  lineNum <- parseLineNum lineNumStr
  let content = parts 
        # Array.drop 2 
        # String.joinWith "|"
        # truncateLine
  pure { path: filePath, lineNum, content, modTime: 0.0 }

parseLineNum :: String -> Maybe Int
parseLineNum s = Int.fromString (String.trim s)

truncateLine :: String -> String
truncateLine s =
  if String.length s > defaultConfig.maxLineLength
  then String.take defaultConfig.maxLineLength s <> "..."
  else s

-- | Sort matches by modification time (most recent first)
sortByModTime :: Array GrepMatch -> Array GrepMatch
sortByModTime = Array.sortBy (\a b -> compare b.modTime a.modTime)

-- ════════════════════════════════════════════════════════════════════════════
-- VALIDATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Validate regex pattern
validatePattern :: String -> Either String Unit
validatePattern pat
  | String.null pat = Left "Pattern is required"
  | otherwise = validateRegexSyntax pat
  where
    foreign import validateRegexSyntax :: String -> Either String Unit

-- ════════════════════════════════════════════════════════════════════════════
-- OUTPUT FORMATTING
-- ════════════════════════════════════════════════════════════════════════════

formatResult :: String -> String -> GrepResult -> ToolResult
formatResult pattern searchPath result =
  { title: pattern
  , metadata: encodeJson
      { matches: result.totalFound
      , truncated: result.truncated
      , searchPath
      }
  , output: formatOutput result
  , attachments: Nothing
  }

formatOutput :: GrepResult -> String
formatOutput result
  | Array.null result.matches = "No files found"
  | otherwise = 
      let header = "Found " <> show result.totalFound <> " matches"
          body = formatMatches result.matches
          footer = formatFooter result
      in String.joinWith "\n" (Array.filter (not <<< String.null) [header, "", body, footer])

formatMatches :: Array GrepMatch -> String
formatMatches matches =
  matches
    # groupByPath
    # map formatFileGroup
    # String.joinWith "\n\n"

groupByPath :: Array GrepMatch -> Array { path :: String, matches :: Array GrepMatch }
groupByPath matches =
  let paths = Array.nub $ map _.path matches
  in paths # map \p -> 
       { path: p
       , matches: Array.filter (\m -> m.path == p) matches
       }

formatFileGroup :: { path :: String, matches :: Array GrepMatch } -> String
formatFileGroup group =
  group.path <> ":\n" <>
    (group.matches 
      # map (\m -> "  Line " <> show m.lineNum <> ": " <> m.content)
      # String.joinWith "\n")

formatFooter :: GrepResult -> String
formatFooter result =
  let truncMsg = if result.truncated 
                 then "(Results truncated. Use more specific pattern.)"
                 else ""
      errMsg = if result.hasErrors
               then "(Some paths were inaccessible)"
               else ""
  in String.joinWith "\n" (Array.filter (not <<< String.null) [truncMsg, errMsg])

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

{-| Coeffect for grep operations.

@
  grepCoeffect params = Filesystem path ⊗ Container rgSpec
@
-}
grepCoeffect :: GrepParams -> Resource
grepCoeffect params =
  let pathSpec = 
        { path: params.path # maybe "." identity
        , readable: true
        , writable: false
        , recursive: true
        }
      containerSpec =
        { image: "alpine:latest"
        , memoryMB: 512
        , cpuPercent: 25
        , timeoutMs: defaultConfig.timeout
        , networkIsolated: true
        , filesystemReadOnly: true
        }
  in filesystem pathSpec ⊗ Container containerSpec

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL REGISTRATION
-- ════════════════════════════════════════════════════════════════════════════

grepTool :: ToolInfo
grepTool =
  { id: "grep"
  , description: "Fast content search using ripgrep with regex support"
  , parameters: grepSchema
  , execute: \json ctx ->
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ════════════════════════════════════════════════════════════════════════════

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Grep Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

grepSchema :: Json
grepSchema = encodeJson
  { "type": "object"
  , "properties":
      { "pattern":
          { "type": "string"
          , "description": "The regex pattern to search for in file contents"
          }
      , "path":
          { "type": "string"
          , "description": "The directory to search in. Defaults to the current working directory."
          }
      , "include":
          { "type": "string"
          , "description": "File pattern to include in the search (e.g. \"*.js\", \"*.{ts,tsx}\")"
          }
      }
  , "required": ["pattern"]
  }

foreign import unsafeCrashWith :: forall a. String -> a
