{-|
Module      : Aleph.Sandbox.GVisor
Description : gVisor runtime management
= gVisor Runtime

This module provides the gVisor (runsc) container runtime integration.
It handles container lifecycle management including creation, execution,
and cleanup.

== gVisor Architecture

@
  +-----------------------------------------------------------+
  |                    Host Kernel                             |
  +-----------------------------------------------------------+
  |  +-----------+  +-----------+  +---------------------+    |
  |  |   runsc   |  |   Gofer   |  |       Sentry        |    |
  |  | (control) |  | (9P proxy)|  | (syscall intercept) |    |
  |  +-----------+  +-----+-----+  +----------+----------+    |
  |                       |                   |               |
  |                       v                   v               |
  |                 +-----------------------------+           |
  |                 |     Sandboxed Process       |           |
  |                 |     (user application)      |           |
  |                 +-----------------------------+           |
  +-----------------------------------------------------------+
@

== Platform Options

| Platform | Description              | Performance | Compatibility |
|----------|--------------------------|-------------|---------------|
| KVM      | Hardware virtualization  | Best        | Requires KVM  |
| PTRACE   | ptrace-based interception| Slower      | Most compat   |
| SYSTRAP  | syscall trap             | Good        | Good          |

== Coeffect Equation

@
  createRuntime : ContainerConfig -> Graded Container GVisorRuntime
  execute : GVisorRuntime -> Command -> Graded (Container * IO) ExecOutput
  destroyRuntime : GVisorRuntime -> Graded Container Unit
@
-}
module Aleph.Sandbox.GVisor
  ( -- * Runtime Handle
    GVisorRuntime(..)
    -- * Runtime Configuration
  , RuntimeConfig(..)
  , Platform(..)
  , NetworkConfig(..)
  , defaultRuntimeConfig
    -- * Lifecycle Management
  , createRuntime
  , destroyRuntime
    -- * Sandboxed Computation
  , Sandboxed(..)
  , runInSandbox
  , withSandbox
    -- * Execution
  , SandboxResult(..)
  , execute
  , executeWithTimeout
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Effect (Effect)
import Effect.Aff (Aff, attempt)
import Effect.Class (liftEffect)
import Data.Unit (Unit, unit)

import Aleph.Sandbox.Types (ContainerConfig, ExecOutput)
import Aleph.Sandbox.Policy (SandboxPolicy, IsolationLevel, deriveIsolationLevel)
import Aleph.Sandbox.Proof (SandboxProof, mkSandboxProof)
import Aleph.Sandbox.GVisor.FFI
  ( createContainer
  , startContainer
  , execInContainer
  , killContainer
  , deleteContainer
  , ContainerId(..)
  , ExecResult(..)
  )

-- ============================================================================
-- GVISOR RUNTIME
-- ============================================================================

{-| gVisor runtime handle.

Represents a running gVisor container managed by runsc.
-}
newtype GVisorRuntime = GVisorRuntime
  { containerId :: String
  , bundlePath :: String
  , socketPath :: String
  , pid :: Int
  , startTime :: Number
  }

-- ============================================================================
-- RUNTIME CONFIGURATION
-- ============================================================================

type RuntimeConfig =
  { runscPath :: String      -- Path to runsc binary
  , rootDir :: String        -- Container root directory
  , logDir :: String         -- Log directory
  , platform :: Platform     -- Execution platform
  , network :: NetworkConfig -- Network configuration
  }

data Platform
  = KVM            -- Hardware virtualization
  | PTRACE         -- ptrace-based (slower, more compatible)
  | SYSTRAP        -- syscall interception

derive instance eqPlatform :: Eq Platform
derive instance genericPlatform :: Generic Platform _

instance showPlatform :: Show Platform where
  show KVM = "KVM"
  show PTRACE = "PTRACE"
  show SYSTRAP = "SYSTRAP"

type NetworkConfig =
  { enableRawSockets :: Boolean
  , enableNetstack :: Boolean  -- gVisor's userspace network stack
  }

-- | Default runtime config
defaultRuntimeConfig :: RuntimeConfig
defaultRuntimeConfig =
  { runscPath: "/usr/local/bin/runsc"
  , rootDir: "/var/run/gvisor"
  , logDir: "/var/log/gvisor"
  , platform: SYSTRAP
  , network:
      { enableRawSockets: false
      , enableNetstack: true
      }
  }

-- ============================================================================
-- LIFECYCLE MANAGEMENT
-- ============================================================================

-- | Create gVisor runtime
createRuntime :: ContainerConfig -> Aff GVisorRuntime
createRuntime config = do
  -- Use default runtime config (can be made configurable later)
  let runtimeConfig = defaultRuntimeConfig
  
  -- 1. Create container (this creates OCI bundle and calls runsc create)
  createResult <- createContainer runtimeConfig config
  case createResult of
    Left err -> liftEffect $ unsafeCrashWith ("Failed to create container: " <> err)
    Right (ContainerId containerId) -> do
      -- 2. Start container
      startResult <- startContainer runtimeConfig (ContainerId containerId)
      case startResult of
        Left err -> liftEffect $ unsafeCrashWith ("Failed to start container: " <> err)
        Right _ -> do
          -- 3. Construct runtime handle
          -- Bundle path is constructed in FFI: rootDir/containerId
          let bundlePath = runtimeConfig.rootDir <> "/" <> containerId
          let socketPath = bundlePath <> "/socket"
          -- Get current timestamp
          startTime <- liftEffect getCurrentTimestamp
          -- Get PID from container status
          pidResult <- getContainerPid runtimeConfig (ContainerId containerId)
          let pid = case pidResult of
                Left _ -> 0  -- Fallback to 0 if PID unavailable
                Right p -> p
          
          pure $ GVisorRuntime
            { containerId: containerId
            , bundlePath: bundlePath
            , socketPath: socketPath
            , pid: pid
            , startTime: startTime
            }

-- | Destroy gVisor runtime
destroyRuntime :: GVisorRuntime -> Aff (Either String Unit)
destroyRuntime (GVisorRuntime rt) = do
  let runtimeConfig = defaultRuntimeConfig
  let containerId = ContainerId rt.containerId
  -- 1. Kill container
  killResult <- killContainer runtimeConfig containerId
  case killResult of
    Left err -> pure $ Left err
    Right _ -> do
      -- 2. Delete container
      deleteResult <- deleteContainer runtimeConfig containerId
      case deleteResult of
        Left err -> pure $ Left err
        Right _ -> pure $ Right unit

-- ============================================================================
-- SANDBOXED COMPUTATION
-- ============================================================================

{-| Sandboxed computation indexed by isolation level.

This is the graded monad over sandbox kinds:

@
  -- In System F-w with kind polymorphism:
  Sandboxed : SandboxKind -> Type -> Type

  -- Laws:
  -- 1. Sandbox kind is preserved through bind
  -- 2. Escape requires proof matching the kind
  -- 3. Composition strengthens to max isolation
@
-}
newtype Sandboxed a = Sandboxed
  { config :: ContainerConfig
  , computation :: GVisorRuntime -> Aff a
  }

-- | Run computation in sandbox
runInSandbox :: forall a. ContainerConfig -> (GVisorRuntime -> Aff a) -> Sandboxed a
runInSandbox config computation = Sandboxed { config, computation }

-- | Execute sandboxed computation with runtime management
withSandbox :: forall a. Sandboxed a -> Aff (SandboxResult a)
withSandbox (Sandboxed { config, computation }) = do
  -- Create runtime
  runtimeResult <- attempt $ createRuntime config
  case runtimeResult of
    Left err -> pure $ SandboxFailure
      { reason: "Failed to create runtime"
      , details: show err
      }
    Right runtime -> do
      -- Execute computation
      result <- attempt $ computation runtime
      -- Always cleanup
      _ <- attempt $ destroyRuntime runtime
      case result of
        Left err -> pure $ SandboxFailure
          { reason: "Computation failed"
          , details: show err
          }
        Right a -> do
          proof <- liftEffect $ mkSandboxProof config runtime
          pure $ SandboxSuccess
            { value: a
            , proof: proof
            }

-- ============================================================================
-- EXECUTION
-- ============================================================================

{-| Result of sandboxed execution.

@
  data SandboxResult a
    = SandboxSuccess { value : a, proof : SandboxProof }
    | SandboxFailure { reason : String, details : String }
    | SandboxTimeout { elapsedMs : Nat }
    | SandboxOOM     { requestedMB : Nat, limitMB : Nat }
@
-}
data SandboxResult a
  = SandboxSuccess { value :: a, proof :: SandboxProof }
  | SandboxFailure { reason :: String, details :: String }
  | SandboxTimeout { elapsedMs :: Int }
  | SandboxOOM { requestedMB :: Int, limitMB :: Int }

derive instance genericSandboxResult :: Generic (SandboxResult a) _

-- | Execute command in sandbox
execute :: RuntimeConfig -> ContainerConfig -> Aff (SandboxResult ExecOutput)
execute runtimeConfig config = 
  withSandbox $ runInSandbox config \runtime -> do
    let containerId = ContainerId runtime.containerId
    execResult <- execInContainer runtimeConfig containerId config.command
    case execResult of
      Left err -> liftEffect $ unsafeCrashWith err
      Right result -> pure
        { stdout: result.stdout
        , stderr: result.stderr
        , exitCode: result.exitCode
        , metrics:
            { wallTimeMs: 0  -- Would measure from start
            , userTimeMs: 0
            , sysTimeMs: 0
            , maxRssMB: 0
            , syscallCount: 0
            }
        }

-- | Execute with explicit timeout
executeWithTimeout :: Int -> ContainerConfig -> Aff (SandboxResult ExecOutput)
executeWithTimeout timeoutMs config =
  execute config { policy = config.policy { timeoutMs = timeoutMs } }

-- ============================================================================
-- HELPERS
-- ============================================================================

notImplemented :: forall a. String -> Aff a
notImplemented name = liftEffect $ unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> Effect a
