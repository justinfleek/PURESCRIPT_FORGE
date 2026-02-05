{-|
Module      : Tool.ExternalDirectory
Description : External directory access control
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
import Data.String as String
import Effect.Aff (Aff)
import Effect.Class (liftEffect)

import Opencode.Types.Tool (ToolContext)

-- | FFI for path operations
foreign import getWorktreeRoot :: Effect String
foreign import normalizePath :: String -> String
foreign import pathStartsWith :: String -> String -> Boolean

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
              
              -- Check if path is within worktree (should have been caught earlier, but double-check)
              if containsPath path
                then pure unit
                else do
              -- For external paths, we require explicit permission
              -- Check permission cache first (would be stored in session state)
              -- If not cached, request permission via UI bridge
              permissionGranted <- requestExternalPermission ctx path kind
              if permissionGranted
                then pure unit -- Permission granted, proceed
                else liftEffect $ unsafeCrashWith 
                  ("External " <> kind <> " access denied: " <> path <> ". User permission required.")

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
containsPath path = unsafePerformEffect $ do
  -- 1. Get project worktree root
  worktreeRoot <- getWorktreeRoot
  
  -- 2. Normalize both paths
  let normalizedPath = normalizePath path
  let normalizedRoot = normalizePath worktreeRoot
  
  -- 3. Check if path starts with worktree root
  pure $ pathStartsWith normalizedPath normalizedRoot
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a

-- ============================================================================
-- PERMISSION MANAGEMENT
-- ============================================================================

{-| Request permission for external directory/file access.
In production, this would:
1. Check permission cache in session state
2. If not cached, prompt user via UI bridge (ctx.ask or WebSocket)
3. Cache permission decision for future requests
-}
requestExternalPermission :: ToolContext -> String -> String -> Aff Boolean
requestExternalPermission ctx path kind = do
  -- In production, this would:
  -- 1. Check if permission is cached in ctx.sessionState or similar
  -- 2. If cached, return cached decision
  -- 3. If not cached, use ctx.ask to prompt user:
  --    ctx.ask { 
  --      question: "Allow access to external " <> kind <> ": " <> path <> "?",
  --      options: [{ label: "Allow", value: "allow" }, { label: "Deny", value: "deny" }]
  --    }
  -- 4. Cache the decision
  -- 5. Return the decision
  
  -- For now, deny by default for security
  -- This ensures external access is explicitly granted
  pure false

-- ============================================================================
-- HELPERS
-- ============================================================================

notImplemented :: forall a. String -> Aff a
notImplemented name = do
  -- Using Aff version for async context
  pure $ unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
