module Nexus.AgentOrchestrator.Sandbox where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Nexus.AgentOrchestrator.Types (AgentType(..), SandboxConfig)
import Nexus.AgentOrchestrator.FFI (callBubblewrap)
import Data.Array as Array

-- | Sandbox instance
type Sandbox =
  { agentId :: String
  , agentType :: AgentType
  , config :: SandboxConfig
  }

-- | Create sandbox for agent
createSandbox :: AgentType -> String -> Maybe SandboxConfig -> Effect Sandbox
createSandbox agentType agentId sandboxConfig = do
  -- Use provided config or get default for agent type
  config <- case sandboxConfig of
    Just cfg -> pure cfg
    Nothing -> getDefaultSandboxConfig agentType agentId
  
  pure { agentId, agentType, config }

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

-- | Launch command in sandbox
-- | Returns process ID on success
launchInSandbox :: Sandbox -> Array String -> Aff (Either String Int)
launchInSandbox sandbox command = do
  -- Build bubblewrap command
  let bwrapArgs = buildBubblewrapArgs sandbox command
  
  -- Call bubblewrap via FFI
  result <- callBubblewrap bwrapArgs
  
  case result of
    Left err -> pure $ Left err
    Right pid -> pure $ Right pid

-- | Build bubblewrap arguments
buildBubblewrapArgs :: Sandbox -> Array String -> Array String
buildBubblewrapArgs sandbox command =
  [ "bwrap" ]
  <> Array.concatMap (\dir ->
        if dir.readOnly then
          [ "--ro-bind", dir.hostPath, dir.sandboxPath ]
        else
          [ "--bind", dir.hostPath, dir.sandboxPath ]
    ) sandbox.config.allowedDirs
  <> [ "--unshare-ipc"
     , "--unshare-pid"
     , "--unshare-uts"
     ]
  <> (if not sandbox.config.networkAccess then [ "--unshare-net" ] else [])
  <> [ "--die-with-parent"
     , "--new-session"
     , "--chdir", sandbox.config.workingDir
     ]
  <> [ "--" ]
  <> command

-- | Call bubblewrap
-- | Returns process ID on success
foreign import callBubblewrap :: Array String -> Aff (Either String Int)
