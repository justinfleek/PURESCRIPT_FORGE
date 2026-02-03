-- | Server context - manages server connections
-- | Migrated from: forge-dev/packages/app/src/context/server.tsx
module App.Context.Server
  ( ServerState
  , StoredProject
  , normalizeServerUrl
  , serverDisplayName
  , projectsKey
  , mkServerState
  ) where

import Prelude

import Data.Array (filter, findIndex)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), Replacement(..), drop, indexOf, length, replace, take, trim)
import Data.String.Regex (regex, test)
import Data.String.Regex.Flags (noFlags)
import Data.Either (either)

-- | Stored project data
type StoredProject =
  { worktree :: String
  , expanded :: Boolean
  }

-- | Server state
type ServerState =
  { list :: Array String
  , projects :: Array { key :: String, projects :: Array StoredProject }
  , lastProject :: Array { key :: String, directory :: String }
  , active :: String
  , healthy :: Maybe Boolean
  }

-- | Create initial server state
mkServerState :: ServerState
mkServerState =
  { list: []
  , projects: []
  , lastProject: []
  , active: ""
  , healthy: Nothing
  }

-- | Normalize a server URL
-- | Ensures http/https prefix and removes trailing slashes
normalizeServerUrl :: String -> Maybe String
normalizeServerUrl input =
  let
    trimmed = trim input
  in
    if trimmed == "" then Nothing
    else
      let
        -- Check if has protocol
        hasProtocol = 
          either (const false) (\r -> test r trimmed)
            (regex "^https?://" noFlags)
        
        withProtocol = 
          if hasProtocol 
          then trimmed 
          else "http://" <> trimmed
        
        -- Remove trailing slashes
        removeTrailingSlashes :: String -> String
        removeTrailingSlashes s =
          let len = length s
          in if len > 0 && take 1 (drop (len - 1) s) == "/" 
             then removeTrailingSlashes (take (len - 1) s)
             else s
      in
        Just (removeTrailingSlashes withProtocol)

-- | Get display name for server URL (without protocol)
serverDisplayName :: String -> String
serverDisplayName url =
  if url == "" then ""
  else
    let
      -- Remove protocol
      withoutProtocol = 
        url
          # replace (Pattern "https://") (Replacement "")
          # replace (Pattern "http://") (Replacement "")
      
      -- Remove trailing slashes
      removeTrailingSlashes :: String -> String
      removeTrailingSlashes s =
        let len = length s
        in if len > 0 && take 1 (drop (len - 1) s) == "/" 
           then removeTrailingSlashes (take (len - 1) s)
           else s
    in
      removeTrailingSlashes withoutProtocol

-- | Get projects key from URL (for grouping projects by server)
projectsKey :: String -> String
projectsKey url =
  if url == "" then ""
  else
    let
      -- Remove protocol
      withoutProtocol = 
        url
          # replace (Pattern "https://") (Replacement "")
          # replace (Pattern "http://") (Replacement "")
      
      -- Get host part (before colon or slash)
      host = 
        case indexOf (Pattern ":") withoutProtocol of
          Just idx -> take idx withoutProtocol
          Nothing -> 
            case indexOf (Pattern "/") withoutProtocol of
              Just idx -> take idx withoutProtocol
              Nothing -> withoutProtocol
    in
      if host == "localhost" || host == "127.0.0.1" 
      then "local"
      else url
