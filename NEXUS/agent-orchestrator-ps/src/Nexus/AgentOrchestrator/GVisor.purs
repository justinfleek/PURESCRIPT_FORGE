module Nexus.AgentOrchestrator.GVisor where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Nexus.AgentOrchestrator.Types (AgentType(..), SandboxConfig)
import Nexus.AgentOrchestrator.GVisor.FFI
  ( createGVisorContainer
  , startGVisorContainer
  , execInGVisorContainer
  , killGVisorContainer
  , deleteGVisorContainer
  , ContainerId(..)
  , ExecResult(..)
  )

-- | gVisor sandbox instance
type GVisorSandbox =
  { agentId :: String
  , agentType :: AgentType
  , config :: SandboxConfig
  , containerId :: Maybe ContainerId
  }

-- | Create gVisor sandbox for agent
createGVisorSandbox :: AgentType -> String -> Maybe SandboxConfig -> Effect GVisorSandbox
createGVisorSandbox agentType agentId sandboxConfig = do
  -- Use provided config or get default for agent type
  config <- case sandboxConfig of
    Just cfg -> pure cfg
    Nothing -> getDefaultSandboxConfig agentType agentId
  
  pure
    { agentId
    , agentType
    , config
    , containerId: Nothing
    }

-- | Get default sandbox config for agent type
getDefaultSandboxConfig :: AgentType -> String -> Effect SandboxConfig
getDefaultSandboxConfig agentType agentId = do
  let baseDir = "/tmp/nexus"
  
  case agentType of
    WebSearch -> pure
      { allowedDirs:
          [ { hostPath: baseDir <> "/agents/" <> agentId
            , sandboxPath: "/tmp/nexus/agents/" <> agentId
            , readOnly: false
            }
          , { hostPath: baseDir <> "/shared/content"
            , sandboxPath: "/tmp/nexus/shared/content"
            , readOnly: false
            }
          , { hostPath: baseDir <> "/shared/semantic-memory"
            , sandboxPath: "/tmp/nexus/shared/semantic-memory"
            , readOnly: true
            }
          ]
      , networkAccess: true
      , workingDir: "/tmp/nexus/agents/" <> agentId
      }
    
    ContentExtraction -> pure
      { allowedDirs:
          [ { hostPath: baseDir <> "/agents/" <> agentId
            , sandboxPath: "/tmp/nexus/agents/" <> agentId
            , readOnly: false
            }
          , { hostPath: baseDir <> "/shared/content"
            , sandboxPath: "/tmp/nexus/shared/content"
            , readOnly: true
            }
          , { hostPath: baseDir <> "/shared/semantic-memory"
            , sandboxPath: "/tmp/nexus/shared/semantic-memory"
            , readOnly: false
            }
          ]
      , networkAccess: false
      , workingDir: "/tmp/nexus/agents/" <> agentId
      }
    
    NetworkFormation -> pure
      { allowedDirs:
          [ { hostPath: baseDir <> "/agents/" <> agentId
            , sandboxPath: "/tmp/nexus/agents/" <> agentId
            , readOnly: false
            }
          , { hostPath: baseDir <> "/shared/semantic-memory"
            , sandboxPath: "/tmp/nexus/shared/semantic-memory"
            , readOnly: true
            }
          , { hostPath: baseDir <> "/shared/network-graph"
            , sandboxPath: "/tmp/nexus/shared/network-graph"
            , readOnly: false
            }
          ]
      , networkAccess: false
      , workingDir: "/tmp/nexus/agents/" <> agentId
      }
    
    DatabaseLayer -> pure
      { allowedDirs:
          [ { hostPath: baseDir <> "/database"
            , sandboxPath: "/tmp/nexus/database"
            , readOnly: false
            }
          , { hostPath: baseDir <> "/shared/semantic-memory"
            , sandboxPath: "/tmp/nexus/shared/semantic-memory"
            , readOnly: false
            }
          , { hostPath: baseDir <> "/shared/network-graph"
            , sandboxPath: "/tmp/nexus/shared/network-graph"
            , readOnly: false
            }
          , { hostPath: baseDir <> "/shared/content"
            , sandboxPath: "/tmp/nexus/shared/content"
            , readOnly: false
            }
          ]
      , networkAccess: false
      , workingDir: "/tmp/nexus/database"
      }

-- | Launch command in gVisor sandbox
-- | Returns container ID and process result on success
launchInGVisorSandbox :: GVisorSandbox -> Array String -> Aff (Either String { containerId :: ContainerId, execResult :: ExecResult })
launchInGVisorSandbox sandbox command = do
  -- Create container
  createResult <- createGVisorContainer sandbox.config sandbox.agentId
  case createResult of
    Left err -> pure $ Left ("Failed to create container: " <> err)
    Right containerId -> do
      -- Start container
      startResult <- startGVisorContainer containerId
      case startResult of
        Left err -> do
          -- Cleanup on failure
          _ <- deleteGVisorContainer containerId
          pure $ Left ("Failed to start container: " <> err)
        Right _ -> do
          -- Execute command
          execResult <- execInGVisorContainer containerId command
          case execResult of
            Left err -> do
              -- Cleanup on failure
              _ <- killGVisorContainer containerId
              _ <- deleteGVisorContainer containerId
              pure $ Left ("Failed to execute command: " <> err)
            Right result -> pure $ Right { containerId, execResult: result }

-- | Destroy gVisor sandbox
destroyGVisorSandbox :: ContainerId -> Aff (Either String Unit)
destroyGVisorSandbox containerId = do
  -- Kill container
  killResult <- killGVisorContainer containerId
  case killResult of
    Left err -> pure $ Left ("Failed to kill container: " <> err)
    Right _ -> do
      -- Delete container
      deleteResult <- deleteGVisorContainer containerId
      case deleteResult of
        Left err -> pure $ Left ("Failed to delete container: " <> err)
        Right _ -> pure $ Right unit
