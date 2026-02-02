{-|
Module      : Tool.ASTEdit.Patch
Description : Multi-file patch application
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Patch Editing Mode

Apply multi-file changes atomically using a simple patch format.

== Coeffect Equation

@
  patch : PatchParams → Graded (Filesystem paths) EditResult

  -- Requires filesystem access to all affected paths
  -- Atomic: all changes succeed or none applied
@

== Patch Format

@
  *** Begin Patch
  *** Add File: <path>
  +line1
  +line2
  *** Update File: <path>
  @@ context line
  -old line
  +new line
  *** Delete File: <path>
  *** End Patch
@

== Operations

| Header      | Description              |
|-------------|--------------------------|
| Add File    | Create new file          |
| Update File | Modify existing file     |
| Delete File | Remove file              |
| Move to     | Rename/move file         |
-}
module Tool.ASTEdit.Patch
  ( -- * Parameters
    PatchParams(..)
    -- * Parsing
  , Hunk(..)
  , HunkType(..)
  , Chunk(..)
  , parsePatch
    -- * Execution
  , applyPatch
    -- * Errors
  , PatchError(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Tuple (Tuple(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)

import Tool.ASTEdit.Types (EditResult, FileChange, ChangeType(..))

-- ════════════════════════════════════════════════════════════════════════════
-- PARAMETERS
-- ════════════════════════════════════════════════════════════════════════════

type PatchParams =
  { patchText :: String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- PATCH TYPES
-- ════════════════════════════════════════════════════════════════════════════

data HunkType
  = HunkAdd
  | HunkUpdate
  | HunkDelete

derive instance eqHunkType :: Eq HunkType
derive instance genericHunkType :: Generic HunkType _

instance showHunkType :: Show HunkType where
  show = genericShow

type Hunk =
  { hunkType :: HunkType
  , path :: String
  , moveTo :: Maybe String
  , chunks :: Array Chunk
  , contents :: String
  }

type Chunk =
  { context :: String
  , deletions :: Array String
  , additions :: Array String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- ERRORS
-- ════════════════════════════════════════════════════════════════════════════

data PatchError
  = EmptyPatch
  | NoHunksFound
  | InvalidHeader String
  | FileNotFound String
  | ContextNotFound String String
  | ParseError String

derive instance eqPatchError :: Eq PatchError
derive instance genericPatchError :: Generic PatchError _

instance showPatchError :: Show PatchError where
  show = genericShow

-- ════════════════════════════════════════════════════════════════════════════
-- PARSING
-- ════════════════════════════════════════════════════════════════════════════

{-| Parse patch text into hunks.

@
  *** Begin Patch
  *** Add File: path/to/file.purs
  +module File where
  +import Prelude
  *** End Patch
@
-}
parsePatch :: String -> Either PatchError (Array Hunk)
parsePatch text = do
  let normalized = String.replaceAll 
        (String.Pattern "\r\n") 
        (String.Replacement "\n") 
        text
  let lines = String.split (String.Pattern "\n") normalized
  
  -- Verify envelope
  case Array.head lines of
    Just "*** Begin Patch" -> pure unit
    _ -> Left (InvalidHeader "Missing *** Begin Patch")
  
  case Array.last lines of
    Just "*** End Patch" -> pure unit
    Just "" -> pure unit  -- trailing newline ok
    _ -> Left (InvalidHeader "Missing *** End Patch")
  
  -- Parse content between envelope
  let content = lines 
        # Array.drop 1 
        # Array.takeWhile (_ /= "*** End Patch")
  
  parseHunks content

parseHunks :: Array String -> Either PatchError (Array Hunk)
parseHunks lines =
  go [] lines
  where
    go acc [] = Right (Array.reverse acc)
    go acc remaining = do
      case parseNextHunk remaining of
        Left err -> Left err
        Right (Tuple hunk rest) ->
          go (Array.cons hunk acc) rest

parseNextHunk :: Array String -> Either PatchError (Tuple Hunk (Array String))
parseNextHunk lines =
  case Array.head lines of
    Nothing -> Left NoHunksFound
    Just line
      | String.take 14 line == "*** Add File: " ->
          let path = String.drop 14 line
              Tuple content rest = takeAddContent (Array.drop 1 lines)
          in Right $ Tuple
              { hunkType: HunkAdd
              , path
              , moveTo: Nothing
              , chunks: []
              , contents: content
              }
              rest
      
      | String.take 17 line == "*** Update File: " ->
          let path = String.drop 17 line
              Tuple chunks rest = takeUpdateChunks (Array.drop 1 lines)
          in Right $ Tuple
              { hunkType: HunkUpdate
              , path
              , moveTo: Nothing
              , chunks
              , contents: ""
              }
              rest
      
      | String.take 17 line == "*** Delete File: " ->
          let path = String.drop 17 line
          in Right $ Tuple
              { hunkType: HunkDelete
              , path
              , moveTo: Nothing
              , chunks: []
              , contents: ""
              }
              (Array.drop 1 lines)
      
      | otherwise -> Left (InvalidHeader line)

takeAddContent :: Array String -> Tuple String (Array String)
takeAddContent lines =
  let content = lines
        # Array.takeWhile (\l -> String.take 1 l == "+" || String.null l)
        # map (\l -> if String.take 1 l == "+" then String.drop 1 l else l)
        # String.joinWith "\n"
      rest = Array.dropWhile (\l -> String.take 1 l == "+" || String.null l) lines
  in Tuple content rest

takeUpdateChunks :: Array String -> Tuple (Array Chunk) (Array String)
takeUpdateChunks lines =
  -- TODO: Parse @@ context, - deletions, + additions
  Tuple [] lines

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

{-| Apply patch to filesystem.

1. Parse patch text
2. Validate all files exist (for update/delete)
3. Validate no conflicts
4. Apply all changes atomically
5. Report results
-}
applyPatch :: PatchParams -> Aff (Either PatchError (Array FileChange))
applyPatch params = do
  case parsePatch params.patchText of
    Left err -> pure $ Left err
    Right hunks -> do
      if Array.null hunks
        then pure $ Left EmptyPatch
        else applyHunks hunks

applyHunks :: Array Hunk -> Aff (Either PatchError (Array FileChange))
applyHunks hunks = do
  -- TODO: Implementation
  -- 1. For each hunk:
  --    - Add: create file with contents
  --    - Update: read file, apply chunks, write
  --    - Delete: remove file
  -- 2. Track all changes for rollback
  -- 3. Report LSP diagnostics
  pure $ Right []
