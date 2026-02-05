{-|
Module      : Sidepanel.Components.Dependency.DependencyManagerTypes
Description : Types for dependency management
Types for dependency analysis and management.
-}
module Sidepanel.Components.Dependency.DependencyManagerTypes where

import Prelude

-- | Dependency information
type DependencyInfo =
  { name :: String
  , version :: String
  , latestVersion :: String
  , vulnerabilities :: Array Vulnerability
  , license :: String
  , used :: Boolean  -- Is dependency actually used?
  , size :: Int  -- Size in bytes
  , description :: Maybe String
  }

-- | Vulnerability information
type Vulnerability =
  { id :: String
  , severity :: VulnerabilitySeverity
  , description :: String
  , fixedIn :: Maybe String  -- Version that fixes the vulnerability
  , cve :: Maybe String  -- CVE identifier
  }

-- | Vulnerability severity
data VulnerabilitySeverity
  = Critical
  | High
  | Medium
  | Low

derive instance eqVulnerabilitySeverity :: Eq VulnerabilitySeverity

-- | Dependency analysis result
type DependencyAnalysis =
  { dependencies :: Array DependencyInfo
  , vulnerabilities :: Array Vulnerability
  , unused :: Array DependencyInfo
  , licenses :: Array LicenseInfo
  , updateSuggestions :: Array UpdateSuggestion
  }

-- | Update suggestion
type UpdateSuggestion =
  { dependency :: String
  , currentVersion :: String
  , latestVersion :: String
  , priority :: Int  -- 1-10, higher is more important
  , breakingChanges :: Boolean
  , description :: String
  }

-- | License information
type LicenseInfo =
  { name :: String
  , license :: String
  , compatible :: Boolean  -- Compatible with project license?
  , restrictions :: Array String  -- License restrictions
  }
