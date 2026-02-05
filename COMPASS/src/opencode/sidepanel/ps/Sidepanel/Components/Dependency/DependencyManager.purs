{-|
Module      : Sidepanel.Components.Dependency.DependencyManager
Description : Dependency management - vulnerability scanning, updates, unused detection
Manages dependencies: analysis, vulnerability scanning, update suggestions, unused detection.
-}
module Sidepanel.Components.Dependency.DependencyManager where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.Dependency.DependencyManagerTypes
  ( DependencyInfo
  , Vulnerability
  , DependencyAnalysis
  , UpdateSuggestion
  , LicenseInfo
  )

-- | Analyze dependencies
analyzeDependencies :: String -> Aff DependencyAnalysis
analyzeDependencies projectRoot = do
  -- Read dependency files
  let dependencies = readDependencies projectRoot
  
  -- Analyze each dependency
  let analyzed = Array.map analyzeDependency dependencies
  
  -- Check for vulnerabilities
  vulnerabilities <- checkVulnerabilities analyzed
  
  -- Find unused dependencies
  let unused = findUnusedDependencies analyzed projectRoot
  
  -- Check licenses
  let licenses = Array.map checkLicense analyzed
  
  pure
    { dependencies: analyzed
    , vulnerabilities: vulnerabilities
    , unused: unused
    , licenses: licenses
    , updateSuggestions: generateUpdateSuggestions analyzed
    }

-- | Read dependencies from config files
readDependencies :: String -> Array String
readDependencies projectRoot = do
  -- Would read package.json, spago.dhall, package.yaml, etc.
  -- For now, return placeholder
  []

-- | Analyze single dependency
analyzeDependency :: String -> DependencyInfo
analyzeDependency depName =
  { name: depName
  , version: "unknown"  -- Would extract from config
  , latestVersion: "unknown"  -- Would fetch from registry
  , vulnerabilities: []
  , license: "unknown"
  , used: true  -- Would check actual usage
  , size: 0  -- Would calculate size
  , description: Nothing
  }

-- | Check vulnerabilities
checkVulnerabilities :: Array DependencyInfo -> Aff (Array Vulnerability)
checkVulnerabilities dependencies = do
  -- Would query vulnerability database (npm audit, etc.)
  -- For now, return placeholder
  pure []

-- | Find unused dependencies
findUnusedDependencies :: Array DependencyInfo -> String -> Array DependencyInfo
findUnusedDependencies dependencies projectRoot = do
  -- Would scan codebase for imports/usage
  -- For now, return empty
  Array.filter (\dep -> not dep.used) dependencies

-- | Check license
checkLicense :: DependencyInfo -> LicenseInfo
checkLicense dep =
  { name: dep.name
  , license: dep.license
  , compatible: true  -- Would check license compatibility
  , restrictions: []
  }

-- | Generate update suggestions
generateUpdateSuggestions :: Array DependencyInfo -> Array UpdateSuggestion
generateUpdateSuggestions dependencies = do
  Array.mapMaybe (\dep ->
    if dep.version /= dep.latestVersion then
      Just
        { dependency: dep.name
        , currentVersion: dep.version
        , latestVersion: dep.latestVersion
        , priority: calculateUpdatePriority dep
        , breakingChanges: false  -- Would check changelog
        , description: "Update available"
        }
    else
      Nothing
  ) dependencies

-- | Calculate update priority
calculateUpdatePriority :: DependencyInfo -> Int
calculateUpdatePriority dep =
  -- Higher priority for security vulnerabilities
  if Array.length dep.vulnerabilities > 0 then
    10
  else
    5
