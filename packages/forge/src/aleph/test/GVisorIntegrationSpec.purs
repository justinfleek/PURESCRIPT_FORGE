{-|
Module      : Forge.Aleph.Sandbox.Test.GVisorIntegrationSpec
Description : Integration tests for gVisor sandbox workflows
Integration tests for complete gVisor workflows: create -> start -> exec -> kill -> delete.
-}
module Forge.Aleph.Sandbox.Test.GVisorIntegrationSpec where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Forge.Aleph.Sandbox.GVisor.FFI
  ( createContainer
  , startContainer
  , execInContainer
  , killContainer
  , deleteContainer
  , getContainerStatus
  , ContainerId(..)
  , ContainerStatus(..)
  , defaultRuntimeConfig
  )

-- ============================================================================
-- TEST FIXTURES
-- ============================================================================

-- | Test container configuration
testContainerConfig :: { image :: String, command :: Array String, workdir :: String, env :: Array { key :: String, value :: String }, mounts :: Array { source :: String, target :: String, readOnly :: Boolean, mountType :: String }, policy :: { allowNetwork :: Boolean, allowFilesystem :: Boolean, allowGPU :: Boolean, allowIPC :: Boolean, maxMemoryMB :: Int, maxCPUPercent :: Int, timeoutMs :: Int }, rootfs :: String, networkMode :: String }
testContainerConfig =
  { image: "alpine:latest"
  , command: ["/bin/sh"]
  , workdir: "/workspace"
  , env: []
  , mounts: []
  , policy: { allowNetwork: false, allowFilesystem: false, allowGPU: false, allowIPC: false, maxMemoryMB: 1024, maxCPUPercent: 25, timeoutMs: 60000 }
  , rootfs: "ReadOnlyRootfs"
  , networkMode: "NoNetwork"
  }

-- ============================================================================
-- INTEGRATION TESTS: FULL WORKFLOWS
-- ============================================================================

-- | Test: Complete container lifecycle
test_completeLifecycle :: Aff Boolean
test_completeLifecycle = do
  let runtimeConfig = defaultRuntimeConfig
  -- Create container
  createResult <- createContainer runtimeConfig testContainerConfig
  case createResult of
    Left _ -> pure false -- Creation failed
    Right containerId -> do
      -- Start container
      startResult <- startContainer runtimeConfig containerId
      case startResult of
        Left _ -> do
          -- Clean up
          _ <- deleteContainer runtimeConfig containerId
          pure false
        Right _ -> do
          -- Check status
          statusResult <- getContainerStatus runtimeConfig containerId
          case statusResult of
            Right _ -> do
              -- Execute command
              execResult <- execInContainer runtimeConfig containerId ["echo", "hello"]
              case execResult of
                Right _ -> do
                  -- Kill container
                  killResult <- killContainer runtimeConfig containerId
                  case killResult of
                    Right _ -> do
                      -- Delete container
                      deleteResult <- deleteContainer runtimeConfig containerId
                      case deleteResult of
                        Right _ -> pure true
                        Left _ -> pure false
                    Left _ -> pure false
                Left _ -> do
                  -- Clean up
                  _ <- killContainer runtimeConfig containerId
                  _ <- deleteContainer runtimeConfig containerId
                  pure false
            _ -> do
              -- Clean up
              _ <- killContainer runtimeConfig containerId
              _ <- deleteContainer runtimeConfig containerId
              pure false

-- | Test: Multiple containers isolation
test_multipleContainersIsolation :: Aff Boolean
test_multipleContainersIsolation = do
  let runtimeConfig = defaultRuntimeConfig
  -- Create two containers
  create1 <- createContainer runtimeConfig testContainerConfig
  create2 <- createContainer runtimeConfig testContainerConfig

  case create1, create2 of
    Right (ContainerId id1), Right (ContainerId id2) -> do
      -- Start both
      start1 <- startContainer runtimeConfig (ContainerId id1)
      start2 <- startContainer runtimeConfig (ContainerId id2)

      case start1, start2 of
        Right _, Right _ -> do
          -- Execute different commands in each
          exec1 <- execInContainer runtimeConfig (ContainerId id1) ["echo", "container1"]
          exec2 <- execInContainer runtimeConfig (ContainerId id2) ["echo", "container2"]

          -- Both should succeed independently
          let bothSucceeded = case exec1, exec2 of
                Right _, Right _ -> true
                _, _ -> false

          -- Clean up
          _ <- killContainer runtimeConfig (ContainerId id1)
          _ <- killContainer runtimeConfig (ContainerId id2)
          _ <- deleteContainer runtimeConfig (ContainerId id1)
          _ <- deleteContainer runtimeConfig (ContainerId id2)

          pure bothSucceeded
        _, _ -> do
          -- Clean up
          _ <- deleteContainer runtimeConfig (ContainerId id1)
          _ <- deleteContainer runtimeConfig (ContainerId id2)
          pure false
    _, _ -> pure false

-- | Test: Container command execution
test_containerCommandExecution :: Aff Boolean
test_containerCommandExecution = do
  let runtimeConfig = defaultRuntimeConfig
  -- Create and start container
  createResult <- createContainer runtimeConfig testContainerConfig
  case createResult of
    Left _ -> pure false
    Right containerId -> do
      startResult <- startContainer runtimeConfig containerId
      case startResult of
        Left _ -> do
          _ <- deleteContainer runtimeConfig containerId
          pure false
        Right _ -> do
          -- Execute multiple commands
          exec1 <- execInContainer runtimeConfig containerId ["echo", "test1"]
          exec2 <- execInContainer runtimeConfig containerId ["echo", "test2"]
          exec3 <- execInContainer runtimeConfig containerId ["ls", "/"]

          -- All should succeed
          let allSucceeded = case exec1, exec2, exec3 of
                Right _, Right _, Right _ -> true
                _, _, _ -> false

          -- Clean up
          _ <- killContainer runtimeConfig containerId
          _ <- deleteContainer runtimeConfig containerId

          pure allSucceeded

-- | Test: Container status transitions
test_containerStatusTransitions :: Aff Boolean
test_containerStatusTransitions = do
  let runtimeConfig = defaultRuntimeConfig
  -- Create container
  createResult <- createContainer runtimeConfig testContainerConfig
  case createResult of
    Left _ -> pure false
    Right containerId -> do
      -- Should have a status after creation
      status1 <- getContainerStatus runtimeConfig containerId
      case status1 of
        Left _ -> do
          _ <- deleteContainer runtimeConfig containerId
          pure false
        Right _ -> do
          -- Start container
          startResult <- startContainer runtimeConfig containerId
          case startResult of
            Left _ -> do
              _ <- deleteContainer runtimeConfig containerId
              pure false
            Right _ -> do
              -- Should have a status after start
              status2 <- getContainerStatus runtimeConfig containerId
              let hasStatus = case status2 of
                    Right _ -> true
                    Left _ -> false

              -- Clean up
              _ <- killContainer runtimeConfig containerId
              _ <- deleteContainer runtimeConfig containerId

              pure hasStatus

-- | Test: Error handling - delete non-existent container
test_errorHandlingDeleteNonExistent :: Aff Boolean
test_errorHandlingDeleteNonExistent = do
  let runtimeConfig = defaultRuntimeConfig
  -- Try to delete non-existent container
  let fakeId = ContainerId "non-existent-container-id"
  deleteResult <- deleteContainer runtimeConfig fakeId

  -- Should fail gracefully
  case deleteResult of
    Left _ -> pure true -- Expected failure
    Right _ -> pure false -- Should not succeed

-- | Test: Error handling - exec in stopped container
test_errorHandlingExecStoppedContainer :: Aff Boolean
test_errorHandlingExecStoppedContainer = do
  let runtimeConfig = defaultRuntimeConfig
  -- Create container but don't start
  createResult <- createContainer runtimeConfig testContainerConfig
  case createResult of
    Left _ -> pure false
    Right containerId -> do
      -- Try to exec in stopped container
      execResult <- execInContainer runtimeConfig containerId ["echo", "test"]

      -- Should fail (container not started)
      let failed = case execResult of
            Left _ -> true
            Right _ -> false

      -- Clean up
      _ <- deleteContainer runtimeConfig containerId

      pure failed

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: Spec Unit
spec = describe "gVisor Integration Tests" do
  describe "Container Lifecycle" do
    it "complete lifecycle: create -> start -> exec -> kill -> delete" do
      result <- test_completeLifecycle
      result `shouldEqual` true

    it "multiple containers isolation" do
      result <- test_multipleContainersIsolation
      result `shouldEqual` true

    it "container command execution" do
      result <- test_containerCommandExecution
      result `shouldEqual` true

    it "container status transitions" do
      result <- test_containerStatusTransitions
      result `shouldEqual` true

  describe "Error Handling" do
    it "handles delete non-existent container gracefully" do
      result <- test_errorHandlingDeleteNonExistent
      result `shouldEqual` true

    it "handles exec in stopped container gracefully" do
      result <- test_errorHandlingExecStoppedContainer
      result `shouldEqual` true
