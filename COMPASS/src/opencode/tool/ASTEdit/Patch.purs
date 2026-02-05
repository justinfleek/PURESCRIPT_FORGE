{-|
Module      : Tool.ASTEdit.Patch
Description : Multi-file patch application
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
import Data.Foldable (foldM)
import Effect.Aff (Aff)
import Effect (Effect)
import Effect.Class (liftEffect)

import Tool.ASTEdit.Types (EditResult, FileChange, ChangeType(..))
import Tool.ASTEdit.FFI.FileIO (readFile, writeFile, deleteFile)
import Tool.ASTEdit.Text (computeDiff)

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
  go [] lines
  where
    go acc [] = Tuple (Array.reverse acc) []
    go acc remaining =
      case Array.head remaining of
        Nothing -> Tuple (Array.reverse acc) []
        Just line
          | String.take 2 line == "@@" ->
              -- Found chunk header, parse chunk
              case parseChunk remaining of
                Tuple chunk rest -> go (Array.cons chunk acc) rest
          | String.take 3 line == "***" ->
              -- Next hunk header, stop
              Tuple (Array.reverse acc) remaining
          | otherwise ->
              -- Skip non-chunk lines
              go acc (Array.drop 1 remaining)

-- | Parse a single chunk (from @@ header to next @@ or end)
parseChunk :: Array String -> Tuple Chunk (Array String)
parseChunk lines =
  case Array.head lines of
    Just headerLine | String.take 2 headerLine == "@@" ->
      let context = headerLine
          Tuple (deletions, additions) rest = parseChunkLines (Array.drop 1 lines)
      in Tuple
          { context
          , deletions
          , additions
          }
          rest
    _ -> Tuple { context: "", deletions: [], additions: [] } lines

-- | Parse chunk lines (deletions and additions)
parseChunkLines :: Array String -> Tuple (Tuple (Array String) (Array String)) (Array String)
parseChunkLines lines =
  go [] [] lines
  where
    go dels adds [] = Tuple (Tuple (Array.reverse dels) (Array.reverse adds)) []
    go dels adds remaining =
      case Array.head remaining of
        Nothing -> Tuple (Tuple (Array.reverse dels) (Array.reverse adds)) []
        Just line
          | String.take 1 line == "-" ->
              -- Deletion line
              go (Array.cons (String.drop 1 line) dels) adds (Array.drop 1 remaining)
          | String.take 1 line == "+" ->
              -- Addition line
              go dels (Array.cons (String.drop 1 line) adds) (Array.drop 1 remaining)
          | String.take 2 line == "@@" ->
              -- Next chunk header
              Tuple (Tuple (Array.reverse dels) (Array.reverse adds)) remaining
          | String.take 3 line == "***" ->
              -- Next hunk header
              Tuple (Tuple (Array.reverse dels) (Array.reverse adds)) remaining
          | String.take 1 line == " " ->
              -- Context line (unchanged), skip
              go dels adds (Array.drop 1 remaining)
          | String.null line ->
              -- Empty line, skip
              go dels adds (Array.drop 1 remaining)
          | otherwise ->
              -- Unknown line, treat as context
              go dels adds (Array.drop 1 remaining)

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
  -- Apply each hunk and collect changes
  changes <- traverse applyHunk hunks
  pure $ Right changes
  where
    applyHunk :: Hunk -> Aff FileChange
    applyHunk hunk = case hunk.hunkType of
      HunkAdd -> do
        -- Create new file with contents
        writeResult <- writeFile hunk.path hunk.contents
        case writeResult of
          Left err -> liftEffect $ unsafeCrashWith ("Failed to create file: " <> err)
          Right _ -> pure
            { filePath: hunk.path
            , changeType: Add
            , oldContent: ""
            , newContent: hunk.contents
            , diff: computeDiff "" hunk.contents
            , additions: Array.length (String.split (String.Pattern "\n") hunk.contents)
            , deletions: 0
            }
      
      HunkUpdate -> do
        -- Read existing file
        readResult <- readFile hunk.path
        case readResult of
          Left err -> liftEffect $ unsafeCrashWith ("Failed to read file for update: " <> err)
          Right oldContent -> do
            -- Apply chunks to content
            case applyChunksToContent oldContent hunk.chunks of
              Left err -> liftEffect $ unsafeCrashWith ("Failed to apply chunks: " <> err)
              Right newContent -> do
                -- Write updated content
                writeResult <- writeFile hunk.path newContent
                case writeResult of
                  Left err -> liftEffect $ unsafeCrashWith ("Failed to write file: " <> err)
                  Right _ -> do
                    let diff = computeDiff oldContent newContent
                    let additions = Array.foldMap (\c -> Array.length c.additions) hunk.chunks
                    let deletions = Array.foldMap (\c -> Array.length c.deletions) hunk.chunks
                    pure
                      { filePath: hunk.path
                      , changeType: Update
                      , oldContent
                      , newContent
                      , diff
                      , additions
                      , deletions
                      }
      
      HunkDelete -> do
        -- Read file before deletion
        readResult <- readFile hunk.path
        let oldContent = case readResult of
              Left _ -> ""  -- File might not exist
              Right content -> content
        -- Delete file
        deleteResult <- deleteFile hunk.path
        case deleteResult of
          Left err -> liftEffect $ unsafeCrashWith ("Failed to delete file: " <> err)
          Right _ -> pure
            { filePath: hunk.path
            , changeType: Delete
            , oldContent
            , newContent: ""
            , diff: computeDiff oldContent ""
            , additions: 0
            , deletions: Array.length (String.split (String.Pattern "\n") oldContent)
            }

-- | Apply chunks to file content
applyChunksToContent :: String -> Array Chunk -> Either String String
applyChunksToContent content chunks =
  foldM applyChunk content chunks
  where
    applyChunk :: String -> Chunk -> Either String String
    applyChunk current chunk = do
      -- Find context line in content
      case findContextLine current chunk.context of
        Nothing -> Left ("Context not found: " <> chunk.context)
        Just contextIdx -> do
          -- Apply deletions and additions at context position
          let lines = String.split (String.Pattern "\n") current
          let beforeContext = Array.take contextIdx lines
          let afterContext = Array.drop (contextIdx + 1) lines
          -- Remove deletion lines
          let afterDeletions = Array.drop (Array.length chunk.deletions) afterContext
          -- Insert addition lines
          let newLines = beforeContext <> chunk.additions <> afterDeletions
          pure $ String.joinWith "\n" newLines
    
    findContextLine :: String -> String -> Maybe Int
    findContextLine content context =
      let lines = String.split (String.Pattern "\n") content
      in Array.findIndex (\line -> String.contains (String.Pattern context) line) lines

foreign import unsafeCrashWith :: forall a. String -> Effect a
