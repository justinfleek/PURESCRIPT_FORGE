{-|
Module      : Forge.Project.VCS
Description : Version Control System Integration

Provides integration with version control systems, primarily Git.
Handles branch detection, status checks, and basic VCS operations.
-}
module Forge.Project.VCS
  ( -- * Types
    VCSType(..)
  , VCSInfo
  , GitStatus
    -- * VCS Detection
  , detect
  , getType
    -- * Git Operations
  , getCurrentBranch
  , getStatus
  , isClean
  , getDiff
  , getUntracked
  , getModified
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | VCS type
data VCSType 
  = Git 
  | Mercurial 
  | SVN 
  | None

derive instance eqVCSType :: Eq VCSType

instance showVCSType :: Show VCSType where
  show Git = "git"
  show Mercurial = "hg"
  show SVN = "svn"
  show None = "none"

-- | VCS info
type VCSInfo =
  { vcsType :: VCSType
  , root :: String
  , branch :: Maybe String
  , isClean :: Boolean
  , remote :: Maybe String
  }

-- | Git status information
type GitStatus =
  { staged :: Array String
  , unstaged :: Array String
  , untracked :: Array String
  , conflicts :: Array String
  , ahead :: Int
  , behind :: Int
  }

-- ============================================================================
-- FFI
-- ============================================================================

foreign import detectVCSFFI :: String -> Aff (Maybe { vcsType :: String, root :: String })
foreign import gitBranchFFI :: String -> Aff (Maybe String)
foreign import gitStatusFFI :: String -> Aff (Either String GitStatus)
foreign import gitDiffFFI :: String -> Maybe String -> Aff (Either String String)
foreign import gitRemoteFFI :: String -> Aff (Maybe String)

-- ============================================================================
-- VCS DETECTION
-- ============================================================================

{-| Detect VCS in directory.

Checks for .git, .hg, .svn directories and returns VCS info.
-}
detect :: String -> Aff (Either String VCSInfo)
detect directory = do
  result <- detectVCSFFI directory
  case result of
    Nothing -> pure $ Right
      { vcsType: None
      , root: directory
      , branch: Nothing
      , isClean: true
      , remote: Nothing
      }
    Just info -> do
      let vcsType = parseVCSType info.vcsType
      branch <- if vcsType == Git then gitBranchFFI info.root else pure Nothing
      clean <- if vcsType == Git then isClean info.root else pure true
      remote <- if vcsType == Git then gitRemoteFFI info.root else pure Nothing
      pure $ Right
        { vcsType
        , root: info.root
        , branch
        , isClean: clean
        , remote
        }

{-| Get VCS type for directory. -}
getType :: String -> Aff VCSType
getType directory = do
  result <- detectVCSFFI directory
  pure $ case result of
    Nothing -> None
    Just info -> parseVCSType info.vcsType

-- ============================================================================
-- GIT OPERATIONS
-- ============================================================================

{-| Get current branch name. -}
getCurrentBranch :: String -> Aff (Maybe String)
getCurrentBranch = gitBranchFFI

{-| Get detailed git status. -}
getStatus :: String -> Aff (Either String GitStatus)
getStatus = gitStatusFFI

{-| Check if working directory is clean. -}
isClean :: String -> Aff Boolean
isClean directory = do
  result <- gitStatusFFI directory
  pure $ case result of
    Left _ -> true  -- Assume clean if error
    Right status -> 
      Array.null status.staged &&
      Array.null status.unstaged &&
      Array.null status.untracked &&
      Array.null status.conflicts

{-| Get diff output.

If a file path is provided, returns diff for that file only.
-}
getDiff :: String -> Maybe String -> Aff (Either String String)
getDiff = gitDiffFFI

{-| Get list of untracked files. -}
getUntracked :: String -> Aff (Array String)
getUntracked directory = do
  result <- gitStatusFFI directory
  pure $ case result of
    Left _ -> []
    Right status -> status.untracked

{-| Get list of modified files (staged and unstaged). -}
getModified :: String -> Aff (Array String)
getModified directory = do
  result <- gitStatusFFI directory
  pure $ case result of
    Left _ -> []
    Right status -> status.staged <> status.unstaged

-- ============================================================================
-- HELPERS
-- ============================================================================

parseVCSType :: String -> VCSType
parseVCSType "git" = Git
parseVCSType "hg" = Mercurial
parseVCSType "svn" = SVN
parseVCSType _ = None
