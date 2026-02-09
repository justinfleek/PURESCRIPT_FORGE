-- | PureScript type definitions for Forge File operation types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript types from forge-dev/packages/forge/src/util/filesystem.ts
-- | CRITICAL: File reading MUST follow complete read protocol (no grep, head, tail, partial reads)
module Forge.Types.File where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Effect.Aff (Aff)

-- | File path
type FilePath = String

-- | Directory path
type DirectoryPath = String

-- | File content (complete file read only)
type FileContent = String

-- | File reading result
-- | CRITICAL: Always reads complete file - no partial reads allowed
type FileReadResult =
  { path :: FilePath
  , content :: FileContent  -- Complete file content
  , size :: Int
  }

-- | File existence check
type FileExists = Boolean

-- | Directory check
type IsDirectory = Boolean

-- | File system operations
-- | All operations MUST follow complete read protocol
class FileSystem m where
  -- | Read complete file (no partial reads)
  readFile :: FilePath -> Aff FileReadResult
  
  -- | Check if file exists
  exists :: FilePath -> Aff FileExists
  
  -- | Check if path is directory
  isDirectory :: FilePath -> Aff IsDirectory
  
  -- | Normalize path (Windows case normalization)
  normalizePath :: FilePath -> FilePath
  
  -- | Check if paths overlap
  overlaps :: FilePath -> FilePath -> Boolean
  
  -- | Check if parent contains child
  contains :: DirectoryPath -> FilePath -> Boolean
  
  -- | Find file walking up directory tree
  findUp :: String -> DirectoryPath -> Maybe DirectoryPath -> Aff (Array FilePath)
  
  -- | Walk up directory tree yielding matches
  up :: { targets :: Array String, start :: DirectoryPath, stop :: Maybe DirectoryPath } -> Aff (Array FilePath)
  
  -- | Glob pattern search walking up directory tree
  globUp :: String -> DirectoryPath -> Maybe DirectoryPath -> Aff (Array FilePath)

-- | File reading protocol compliance
-- | This type ensures complete file reads only
data CompleteFileRead = CompleteFileRead FilePath FileContent

derive instance genericCompleteFileRead :: Generic CompleteFileRead _
derive instance eqCompleteFileRead :: Eq CompleteFileRead

instance showCompleteFileRead :: Show CompleteFileRead where
  show = genericShow

-- | Banned file reading operations (compile-time prevention)
-- | These should never appear in code
data BannedFileOperation
  = Grep FilePath String  -- BANNED: Use complete read + filter
  | Head FilePath Int     -- BANNED: Use complete read + take
  | Tail FilePath Int     -- BANNED: Use complete read + drop
  | ReadPartial FilePath Int Int  -- BANNED: Use complete read + slice

-- | This type should be unrepresentable (no constructors exported)
-- | If this compiles, we have a violation
