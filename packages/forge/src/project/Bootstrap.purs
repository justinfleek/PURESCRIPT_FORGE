{-|
Module      : Forge.Project.Bootstrap
Description : Project Bootstrap

Initializes a project directory with Forge configuration and
necessary files.

== Bootstrap Process

1. Detect project type (git repo, npm project, etc.)
2. Create .forge directory structure
3. Initialize configuration files
4. Set up any needed integrations
-}
module Forge.Project.Bootstrap
  ( -- * Types
    BootstrapConfig
  , BootstrapResult
  , ProjectType(..)
  , InstanceBootstrap
    -- * Bootstrap Operations
  , bootstrap
  , bootstrapWithConfig
  , isBootstrapped
    -- * Project Detection
  , detectProjectType
  , getProjectInfo
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Project type detection
data ProjectType
  = NodeProject       -- Has package.json
  | RustProject       -- Has Cargo.toml
  | PythonProject     -- Has pyproject.toml or setup.py
  | GoProject         -- Has go.mod
  | HaskellProject    -- Has cabal or stack file
  | PureScriptProject -- Has spago.yaml or spago.dhall
  | GenericProject    -- No specific type detected
  | GitRepo           -- Has .git directory

derive instance eqProjectType :: Eq ProjectType

instance showProjectType :: Show ProjectType where
  show NodeProject = "node"
  show RustProject = "rust"
  show PythonProject = "python"
  show GoProject = "go"
  show HaskellProject = "haskell"
  show PureScriptProject = "purescript"
  show GenericProject = "generic"
  show GitRepo = "git"

-- | Bootstrap configuration
type BootstrapConfig =
  { createGitignore :: Boolean
  , initializeConfig :: Boolean
  , createAgentsDir :: Boolean
  , createSkillsDir :: Boolean
  }

-- | Bootstrap result
type BootstrapResult =
  { success :: Boolean
  , directory :: String
  , projectType :: ProjectType
  , filesCreated :: Array String
  , errors :: Array String
  }

-- | Instance bootstrap type alias
type InstanceBootstrap = Unit

-- ============================================================================
-- FFI
-- ============================================================================

-- | Check if file/directory exists
foreign import existsFFI :: String -> Aff Boolean

-- | Create directory
foreign import mkdirFFI :: String -> Aff (Either String Unit)

-- | Write file
foreign import writeFileFFI :: String -> String -> Aff (Either String Unit)

-- | List directory
foreign import listDirFFI :: String -> Aff (Either String (Array String))

-- ============================================================================
-- DEFAULT CONFIG
-- ============================================================================

defaultConfig :: BootstrapConfig
defaultConfig =
  { createGitignore: true
  , initializeConfig: true
  , createAgentsDir: true
  , createSkillsDir: true
  }

-- ============================================================================
-- BOOTSTRAP OPERATIONS
-- ============================================================================

{-| Bootstrap a project directory.

Creates the .forge directory structure with default configuration.
-}
bootstrap :: String -> Aff (Either String Unit)
bootstrap directory = do
  result <- bootstrapWithConfig directory defaultConfig
  if result.success
    then pure $ Right unit
    else pure $ Left (Array.head result.errors # fromMaybe "Bootstrap failed")
  where
    fromMaybe def Nothing = def
    fromMaybe _ (Just x) = x

{-| Bootstrap with custom configuration. -}
bootstrapWithConfig :: String -> BootstrapConfig -> Aff BootstrapResult
bootstrapWithConfig directory config = do
  -- Detect project type
  projectType <- detectProjectType directory
  
  -- Create .forge directory
  let forgeDir = directory <> "/.forge"
  mkdirResult <- mkdirFFI forgeDir
  
  case mkdirResult of
    Left err -> pure 
      { success: false
      , directory
      , projectType
      , filesCreated: []
      , errors: [err]
      }
    Right _ -> do
      -- Create subdirectories and files
      filesCreated <- createStructure directory config
      
      pure
        { success: true
        , directory
        , projectType
        , filesCreated
        , errors: []
        }

{-| Check if a directory is already bootstrapped. -}
isBootstrapped :: String -> Aff Boolean
isBootstrapped directory = existsFFI (directory <> "/.forge")

-- ============================================================================
-- PROJECT DETECTION
-- ============================================================================

{-| Detect the project type from files present. -}
detectProjectType :: String -> Aff ProjectType
detectProjectType directory = do
  -- Check for various project markers
  hasPackageJson <- existsFFI (directory <> "/package.json")
  hasCargoToml <- existsFFI (directory <> "/Cargo.toml")
  hasPyproject <- existsFFI (directory <> "/pyproject.toml")
  hasGoMod <- existsFFI (directory <> "/go.mod")
  hasCabal <- existsFFI (directory <> "/*.cabal")
  hasSpago <- existsFFI (directory <> "/spago.yaml")
  hasGit <- existsFFI (directory <> "/.git")
  
  pure $ case unit of
    _ | hasPackageJson -> NodeProject
    _ | hasCargoToml -> RustProject
    _ | hasPyproject -> PythonProject
    _ | hasGoMod -> GoProject
    _ | hasCabal -> HaskellProject
    _ | hasSpago -> PureScriptProject
    _ | hasGit -> GitRepo
    _ -> GenericProject

{-| Get basic project information. -}
getProjectInfo :: String -> Aff { name :: String, projectType :: ProjectType }
getProjectInfo directory = do
  projectType <- detectProjectType directory
  -- Extract project name from directory path
  let parts = splitPath directory
      name = Array.last parts # fromMaybe "project"
  pure { name, projectType }
  where
    splitPath s = Array.filter (not <<< eq "") $ 
                  Array.concatMap (Array.singleton) $
                  map identity $ 
                  splitImpl s
    
    fromMaybe def Nothing = def
    fromMaybe _ (Just x) = x

foreign import splitImpl :: String -> Array String

-- ============================================================================
-- HELPERS
-- ============================================================================

createStructure :: String -> BootstrapConfig -> Aff (Array String)
createStructure directory config = do
  let forgeDir = directory <> "/.forge"
  created <- pure []
  
  -- Create agents directory
  created' <- if config.createAgentsDir
    then do
      _ <- mkdirFFI (forgeDir <> "/agents")
      pure $ created <> [forgeDir <> "/agents"]
    else pure created
  
  -- Create skills directory
  created'' <- if config.createSkillsDir
    then do
      _ <- mkdirFFI (forgeDir <> "/skills")
      pure $ created' <> [forgeDir <> "/skills"]
    else pure created'
  
  -- Create config file
  created''' <- if config.initializeConfig
    then do
      _ <- writeFileFFI (forgeDir <> "/config.json") defaultConfigJson
      pure $ created'' <> [forgeDir <> "/config.json"]
    else pure created''
  
  pure created'''

defaultConfigJson :: String
defaultConfigJson = """
{
  "version": "1.0",
  "provider": "anthropic",
  "model": "claude-sonnet-4-20250514",
  "features": {
    "streaming": true,
    "tools": true
  }
}
"""
