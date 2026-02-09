-- | Configuration Loading - Environment-Based Server Configuration
-- |
-- | **What:** Loads Bridge Server configuration from environment variables with
-- |         validation and default values. Provides type-safe configuration access.
-- | **Why:** Centralizes configuration management, ensuring all settings are validated
-- |         and have sensible defaults. Enables configuration via environment variables
-- |         for deployment flexibility.
-- | **How:** Reads environment variables, validates values (ranges, non-empty, etc.),
-- |         and falls back to defaults if values are missing or invalid.
-- |
-- | **Dependencies:**
-- | - `Bridge.FFI.Node.Process`: Environment variable access
-- | - `Bridge.Utils.Validation`: Validation functions
-- |
-- | **Configuration Sources:**
-- | - Environment variables (primary)
-- | - Default values (fallback)
-- |
-- | **Environment Variables:**
-- | - `SIDEPANEL_PORT`: Server port (default: 8765)
-- | - `SIDEPANEL_HOST`: Server host (default: "127.0.0.1")
-- | - `STATIC_DIR`: Static file directory (default: "./dist")
-- | - `VENICE_API_KEY`: Venice API key (optional)
-- | - `OPENCODE_API_URL`: Forge API URL (default: "http://forge.internal")
-- | - `OPENCODE_DIRECTORY`: Forge directory (default: "./")
-- | - `STORAGE_PATH`: SQLite database path (default: "./bridge.db")
-- | - `ANALYTICS_PATH`: DuckDB analytics path (default: "./analytics.duckdb")
-- | - `SYNC_INTERVAL_MINUTES`: Database sync interval (default: 60)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Forge.Config as Config
-- |
-- | -- Load configuration
-- | config <- Config.loadConfig
-- |
-- | -- Use configuration
-- | port = config.port
-- | veniceApiKey = config.venice.apiKey
-- | ```
module Forge.Config where

import Prelude
import Effect (Effect)
import Data.Int (fromString)
import Data.Maybe (Maybe(..), fromMaybe)
import Forge.Bridge.FFI.Node.Process (getEnv)
import Forge.Bridge.Utils.Validation (validateNonNegative, validatePositive, validateNonEmpty, validateRange)

-- | Configuration type
type Config =
  { port :: Int
  , host :: String
  , staticDir :: String
  , venice ::
      { apiKey :: Maybe String
      }
  , forge ::
      { apiUrl :: String
      , directory :: String
      }
  , lean ::
      { enabled :: Boolean
      , command :: String
      , args :: Array String
      }
  , storage ::
      { path :: String
      , analyticsPath :: String
      , syncIntervalMinutes :: Int
      }
  }

-- | Load configuration from environment - Read and validate configuration
-- |
-- | **Purpose:** Loads configuration from environment variables, validates values,
-- |             and returns Config with defaults for missing/invalid values.
-- | **Returns:** Config with all fields populated
-- | **Side Effects:** Reads environment variables
-- |
-- | **Validation:**
-- | - Port: Validated to be in range 1-65535, defaults to 8765
-- | - Host: Validated to be non-empty, defaults to "127.0.0.1"
-- | - Paths: Validated to be non-empty, defaults provided
-- | - Sync interval: Validated to be positive, defaults to 60 minutes
-- |
-- | **Example:**
-- | ```purescript
-- | config <- loadConfig
-- | ```
loadConfig :: Effect Config
loadConfig = do
  portEnv <- getEnv "SIDEPANEL_PORT"
  let portRaw = fromMaybe 8765 $ portEnv >>= fromString
  let port = if validateRange 1.0 65535.0 (fromInt portRaw) then portRaw else 8765
  
  hostEnv <- getEnv "SIDEPANEL_HOST"
  let hostRaw = fromMaybe "127.0.0.1" hostEnv
  let host = if validateNonEmpty hostRaw then hostRaw else "127.0.0.1"
  
  staticDirEnv <- getEnv "STATIC_DIR"
  let staticDirRaw = fromMaybe "./dist" staticDirEnv
  let staticDir = if validateNonEmpty staticDirRaw then staticDirRaw else "./dist"
  
  veniceApiKey <- getEnv "VENICE_API_KEY"
  
  forgeApiUrlEnv <- getEnv "OPENCODE_API_URL"
  let forgeApiUrlRaw = fromMaybe "http://forge.internal" forgeApiUrlEnv
  let forgeApiUrl = if validateNonEmpty forgeApiUrlRaw then forgeApiUrlRaw else "http://forge.internal"
  
  forgeDirEnv <- getEnv "OPENCODE_DIRECTORY"
  let forgeDirRaw = fromMaybe "./" forgeDirEnv
  let forgeDir = if validateNonEmpty forgeDirRaw then forgeDirRaw else "./"
  
  storagePathEnv <- getEnv "STORAGE_PATH"
  let storagePathRaw = fromMaybe "./bridge.db" storagePathEnv
  let storagePath = if validateNonEmpty storagePathRaw then storagePathRaw else "./bridge.db"
  
  analyticsPathEnv <- getEnv "ANALYTICS_PATH"
  let analyticsPathRaw = fromMaybe "./analytics.duckdb" analyticsPathEnv
  let analyticsPath = if validateNonEmpty analyticsPathRaw then analyticsPathRaw else "./analytics.duckdb"
  
  syncIntervalEnv <- getEnv "SYNC_INTERVAL_MINUTES"
  let syncIntervalRaw = fromMaybe 60 $ syncIntervalEnv >>= fromString
  let syncIntervalMinutes = if validatePositive (fromInt syncIntervalRaw) then syncIntervalRaw else 60
  
  pure
    { port
    , host
    , staticDir
    , venice: { apiKey: veniceApiKey }
    , forge:
        { apiUrl: forgeApiUrl
        , directory: forgeDir
        }
    , lean:
        { enabled: false
        , command: "lean-lsp-mcp"
        , args: []
        }
    , storage: 
        { path: storagePath
        , analyticsPath: analyticsPath
        , syncIntervalMinutes: syncIntervalMinutes
        }
    }

foreign import fromInt :: Int -> Number

