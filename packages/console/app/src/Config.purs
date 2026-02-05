-- | Console Application Configuration
-- |
-- | Application-wide constants and configuration values.
-- | Pure data - no FFI, no effects.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/config.ts
-- | Migrated: 2026-02-03
module Console.App.Config
  ( Config
  , GitHubConfig
  , SocialConfig
  , StatsConfig
  , config
  , baseUrl
  , github
  , social
  , stats
  ) where

import Prelude

-- | GitHub repository configuration
type GitHubConfig =
  { repoUrl :: String
  , starsFormatted :: 
      { compact :: String
      , full :: String
      }
  }

-- | Social media links
type SocialConfig =
  { twitter :: String
  , discord :: String
  }

-- | Static statistics for landing page
type StatsConfig =
  { contributors :: String
  , commits :: String
  , monthlyUsers :: String
  }

-- | Complete application configuration
type Config =
  { baseUrl :: String
  , github :: GitHubConfig
  , social :: SocialConfig
  , stats :: StatsConfig
  }

-- | Base URL for the application
baseUrl :: String
baseUrl = "https://opencode.ai"

-- | GitHub repository configuration
github :: GitHubConfig
github =
  { repoUrl: "https://github.com/anomalyco/opencode"
  , starsFormatted:
      { compact: "80K"
      , full: "80,000"
      }
  }

-- | Social media links
social :: SocialConfig
social =
  { twitter: "https://x.com/opencode"
  , discord: "https://discord.gg/opencode"
  }

-- | Static statistics
stats :: StatsConfig
stats =
  { contributors: "600"
  , commits: "7,500"
  , monthlyUsers: "1.5M"
  }

-- | Complete configuration record
config :: Config
config =
  { baseUrl
  , github
  , social
  , stats
  }
