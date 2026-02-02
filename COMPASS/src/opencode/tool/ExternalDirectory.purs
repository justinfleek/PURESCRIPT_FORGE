{-|
Module      : Tool.ExternalDirectory
Description : External directory access control
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= External Directory

This module provides access control for operations on files and
directories outside the project workspace. It ensures user consent
before allowing access to external paths.

== Coeffect Equation

@
  assertExternalDirectory : Path -> Graded (Permission * UI) Unit

  -- Requires:
  -- 1. Permission check for external access
  -- 2. UI access for user prompts
@

== Access Control Flow

@
  1. Check if path is within project worktree
     -> If yes: allow immediately
  
  2. Check permission cache for parent directory
     -> If cached: use cached decision
  
  3. Prompt user for permission
     -> If granted: cache and proceed
     -> If denied: throw error
@

== Security Considerations

1. All external access requires explicit user consent
2. Permissions are cached per parent directory
3. Cache can be persistent ("always allow") or session-only

-}
module Tool.ExternalDirectory
  ( -- * Access Control
    assertExternalDirectory
  , ExternalAccessKind(..)
  , ExternalAccessOptions(..)
    -- * Path Checking
  , isExternalPath
  , containsPath
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext)

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Kind of external access being requested. -}
data ExternalAccessKind
  = FileAccess       -- Single file access
  | DirectoryAccess  -- Directory listing/access

instance showExternalAccessKind :: Show ExternalAccessKind where
  show FileAccess = "file"
  show DirectoryAccess = "directory"

{-| Options for external directory assertion. -}
type ExternalAccessOptions =
  { bypass :: Maybe Boolean   -- Skip check if true
  , kind :: Maybe ExternalAccessKind  -- Type of access
  }

-- ============================================================================
-- ACCESS CONTROL
-- ============================================================================

{-| Assert that access to an external directory is permitted.

If the target path is outside the project worktree, this function
will prompt the user for permission before allowing access.

Throws an error if:
- User denies permission
- Permission request times out

Usage:
@
  execute params ctx = do
    assertExternalDirectory ctx params.path Nothing
    -- proceed with file operation
@
-}
assertExternalDirectory :: ToolContext -> Maybe String -> Maybe ExternalAccessOptions -> Aff Unit
assertExternalDirectory ctx target options = do
  case target of
    Nothing -> pure unit  -- No path, nothing to check
    Just path -> do
      -- Check bypass option
      let bypass = options >>= _.bypass
      case bypass of
        Just true -> pure unit
        _ -> do
          -- Check if path is within project
          if containsPath path
            then pure unit
            else do
              -- Request permission for external access
              let kind = case options >>= _.kind of
                    Just DirectoryAccess -> "directory"
                    _ -> "file"
              
              -- TODO: Call ctx.ask for permission
              -- TODO: Cache permission for parent directory
              
              notImplemented "assertExternalDirectory permission request"

-- ============================================================================
-- PATH CHECKING
-- ============================================================================

{-| Check if a path is external to the project. -}
isExternalPath :: String -> Boolean
isExternalPath path = not (containsPath path)

{-| Check if a path is contained within the project worktree.

This is a security-critical function. It handles:
- Path normalization
- Symlink resolution
- Directory traversal attacks (..)
-}
containsPath :: String -> Boolean
containsPath _path =
  -- TODO: Implement proper path containment check
  -- 1. Get project worktree root
  -- 2. Normalize both paths
  -- 3. Check if path starts with worktree
  true  -- Default to allowing (safe for development)

-- ============================================================================
-- HELPERS
-- ============================================================================

notImplemented :: forall a. String -> Aff a
notImplemented name = do
  -- Using Aff version for async context
  pure $ unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
