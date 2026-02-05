{-|
Module      : Aleph.Sandbox.Test.GVisorIntegrationSpec
Description : Integration tests for gVisor sandbox workflows
Integration tests for complete gVisor workflows: create → start → exec → kill → delete.
-}
module Aleph.Sandbox.Test.GVisorIntegrationSpec where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff, delay, Milliseconds(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Aleph.Sandbox.GVisor
  ( createContainer
  , startContainer
  , execInContainer
  , killContainer
  , deleteContainer
  , getContainerStatus
  , ContainerId(..)
  , ContainerStatus(..)
  )

-- ============================================================================
-- TEST FIXTURES
-- ============================================================================

-- | Test OCI bundle path (would be created in real tests)
testBundlePath :: String
testBundlePath = "/tmp/test-bundle"

-- ============================================================================
-- INTEGRATION TESTS: FULL WORKFLOWS
-- ============================================================================

-- | Test: Complete container lifecycle
test_completeLifecycle :: Aff Boolean
test_completeLifecycle = do
  -- Create container
  createResult <- createContainer testBundlePath "test-container"
  case createResult of
    Left _ -> pure false -- Creation failed
    Right containerId -> do
      -- Start container
      startResult <- startContainer containerId
      case startResult of
        Left _ -> do
          -- Clean up
          deleteContainer containerId
          pure false
        Right _ -> do
          -- Check status
          statusResult <- getContainerStatus containerId
          case statusResult of
            Right Running -> do
              -- Execute command
              execResult <- execInContainer containerId "echo" ["hello"]
              case execResult of
                Right _ -> do
                  -- Kill container
                  killResult <- killContainer containerId
                  case killResult of
                    Right _ -> do
                      -- Delete container
                      deleteResult <- deleteContainer containerId
                      case deleteResult of
                        Right _ -> pure true
                        Left _ -> pure false
                    Left _ -> pure false
                Left _ -> do
                  -- Clean up
                  killContainer containerId
                  deleteContainer containerId
                  pure false
            _ -> do
              -- Clean up
              killContainer containerId
              deleteContainer containerId
              pure false

-- | Test: Multiple containers isolation
test_multipleContainersIsolation :: Aff Boolean
test_multipleContainersIsolation = do
  -- Create two containers
  create1 <- createContainer (testBundlePath <> "1") "test-container-1"
  create2 <- createContainer (testBundlePath <> "2") "test-container-2"
  
  case create1, create2 of
    Right (ContainerId id1), Right (ContainerId id2) -> do
      -- Start both
      start1 <- startContainer (ContainerId id1)
      start2 <- startContainer (ContainerId id2)
      
      case start1, start2 of
        Right _, Right _ -> do
          -- Execute different commands in each
          exec1 <- execInContainer (ContainerId id1) "echo" ["container1"]
          exec2 <- execInContainer (ContainerId id2) "echo" ["container2"]
          
          -- Both should succeed independently
          let bothSucceeded = case exec1, exec2 of
                Right _, Right _ -> true
                _, _ -> false
          
          -- Clean up
          killContainer (ContainerId id1)
          killContainer (ContainerId id2)
          deleteContainer (ContainerId id1)
          deleteContainer (ContainerId id2)
          
          pure bothSucceeded
        _, _ -> do
          -- Clean up
          deleteContainer (ContainerId id1)
          deleteContainer (ContainerId id2)
          pure false
    _, _ -> pure false

-- | Test: Container command execution
test_containerCommandExecution :: Aff Boolean
test_containerCommandExecution = do
  -- Create and start container
  createResult <- createContainer testBundlePath "test-exec"
  case createResult of
    Left _ -> pure false
    Right containerId -> do
      startResult <- startContainer containerId
      case startResult of
        Left _ -> do
          deleteContainer containerId
          pure false
        Right _ -> do
          -- Execute multiple commands
          exec1 <- execInContainer containerId "echo" ["test1"]
          exec2 <- execInContainer containerId "echo" ["test2"]
          exec3 <- execInContainer containerId "ls" ["/"]
          
          -- All should succeed
          let allSucceeded = case exec1, exec2, exec3 of
                Right _, Right _, Right _ -> true
                _, _, _ -> false
          
          -- Clean up
          killContainer containerId
          deleteContainer containerId
          
          pure allSucceeded

-- | Test: Container status transitions
test_containerStatusTransitions :: Aff Boolean
test_containerStatusTransitions = do
  -- Create container
  createResult <- createContainer testBundlePath "test-status"
  case createResult of
    Left _ -> pure false
    Right containerId -> do
      -- Should be Created
      status1 <- getContainerStatus containerId
      let isCreated = case status1 of
            Right Created -> true
            _ -> false
      
      if not isCreated then do
        deleteContainer containerId
        pure false
      else do
        -- Start container
        startResult <- startContainer containerId
        case startResult of
          Left _ -> do
            deleteContainer containerId
            pure false
          Right _ -> do
            -- Should be Running
            status2 <- getContainerStatus containerId
            let isRunning = case status2 of
                  Right Running -> true
                  _ -> false
            
            -- Clean up
            killContainer containerId
            deleteContainer containerId
            
            pure isRunning

-- | Test: Error handling - delete non-existent container
test_errorHandlingDeleteNonExistent :: Aff Boolean
test_errorHandlingDeleteNonExistent = do
  -- Try to delete non-existent container
  let fakeId = ContainerId "non-existent-container-id"
  deleteResult <- deleteContainer fakeId
  
  -- Should fail gracefully
  case deleteResult of
    Left _ -> pure true -- Expected failure
    Right _ -> pure false -- Should not succeed

-- | Test: Error handling - exec in stopped container
test_errorHandlingExecStoppedContainer :: Aff Boolean
test_errorHandlingExecStoppedContainer = do
  -- Create container but don't start
  createResult <- createContainer testBundlePath "test-stopped"
  case createResult of
    Left _ -> pure false
    Right containerId -> do
      -- Try to exec in stopped container
      execResult <- execInContainer containerId "echo" ["test"]
      
      -- Should fail (container not started)
      let failed = case execResult of
            Left _ -> true
            Right _ -> false
      
      -- Clean up
      deleteContainer containerId
      
      pure failed

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: Spec Unit
spec = describe "gVisor Integration Tests" do
  describe "Container Lifecycle" do
    it "complete lifecycle: create → start → exec → kill → delete" do
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
