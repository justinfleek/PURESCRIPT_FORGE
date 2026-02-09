-- | Configuration Loading - Environment-Based Server Configuration
-- | Loads Bridge Server configuration from environment variables
module Bridge.Config where

import Prelude
import Effect (Effect)
import Data.Int (fromString)
import Data.Maybe (Maybe(..), fromMaybe)
import Bridge.FFI.Node.Process (getEnv)

-- | Configuration type
type Config =
  { port :: Int
  , host :: String
  , staticDir :: String
  , databaseUrl :: Maybe String
  , region :: String
  }

-- | Load configuration from environment
loadConfig :: Effect Config
loadConfig = do
  portEnv <- getEnv "PORT"
  let port = fromMaybe 8080 $ portEnv >>= fromString
  
  hostEnv <- getEnv "HOST"
  let host = fromMaybe "0.0.0.0" hostEnv
  
  staticDirEnv <- getEnv "STATIC_DIR"
  let staticDir = fromMaybe "./dist" staticDirEnv
  
  databaseUrl <- getEnv "DATABASE_URL"
  
  regionEnv <- getEnv "REGION"
  let region = fromMaybe "iad" regionEnv
  
  pure
    { port
    , host
    , staticDir
    , databaseUrl
    , region
    }
