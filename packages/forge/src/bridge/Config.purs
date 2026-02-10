-- | Bridge Configuration
-- | Environment-based configuration loading with defaults and validation
module Bridge.Config where

import Prelude
import Effect (Effect)
import Data.Int (fromString) as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Bridge.FFI.Node.Process (getEnv)
import Bridge.Utils.Validation (validateNonEmpty, validatePositive, validateRange)

-- | Bridge server configuration
type Config =
  { port :: Int
  , host :: String
  , staticDir :: String
  , venice ::
      { apiKey :: Maybe String
      }
  , opencode ::
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

-- | Load configuration from environment variables with defaults
loadConfig :: Effect Config
loadConfig = do
  portStr <- getEnv "SIDEPANEL_PORT"
  host <- getEnv "SIDEPANEL_HOST"
  staticDir <- getEnv "STATIC_DIR"
  veniceApiKey <- getEnv "VENICE_API_KEY"
  opencodeApiUrl <- getEnv "OPENCODE_API_URL"
  opencodeDirectory <- getEnv "OPENCODE_DIRECTORY"
  storagePath <- getEnv "STORAGE_PATH"
  analyticsPath <- getEnv "ANALYTICS_PATH"
  syncIntervalStr <- getEnv "SYNC_INTERVAL_MINUTES"
  leanEnabled <- getEnv "LEAN_ENABLED"
  leanCommand <- getEnv "LEAN_COMMAND"

  let port = fromMaybe 3000 (portStr >>= Int.fromString)
  let syncInterval = fromMaybe 5 (syncIntervalStr >>= Int.fromString)

  pure
    { port: if validateRange 1.0 65535.0 (intToNumber port) then port else 3000
    , host: fromMaybe "localhost" host
    , staticDir: fromMaybe "./static" staticDir
    , venice:
        { apiKey: veniceApiKey
        }
    , opencode:
        { apiUrl: fromMaybe "http://localhost:1337" opencodeApiUrl
        , directory: fromMaybe "." opencodeDirectory
        }
    , lean:
        { enabled: fromMaybe "false" leanEnabled == "true"
        , command: fromMaybe "lean" leanCommand
        , args: ["--server"]
        }
    , storage:
        { path: fromMaybe "./data/bridge.db" storagePath
        , analyticsPath: fromMaybe "./data/analytics.duckdb" analyticsPath
        , syncIntervalMinutes: if validatePositive (intToNumber syncInterval) then syncInterval else 5
        }
    }

-- | Convert Int to Number
foreign import intToNumber :: Int -> Number
