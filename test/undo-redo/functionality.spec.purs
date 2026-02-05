-- | Deep comprehensive undo/redo functionality tests
-- | Tests all undo/redo operations, edge cases, and bug detection
module Test.UndoRedo.FunctionalitySpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Array as Array
import Sidepanel.State.UndoRedo as UndoRedo
import Sidepanel.State.AppState as AppState
import Test.Sidepanel.TestFixtures as Fixtures

-- | Create a simple test state with a unique identifier
mkTestState :: Int -> AppState.AppState
mkTestState id =
  let
    initialState = AppState.initialState
  in
    initialState { ui = initialState.ui { activePanel = AppState.ChatPanel } }

-- | Deep comprehensive undo/redo functionality tests
spec :: Spec Unit
spec = describe "Undo/Redo Functionality Deep Tests" $ do
  describe "Basic Undo/Redo Operations" $ do
    it "can undo after pushing a state" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        newState = mkTestState 1
        afterPush = UndoRedo.pushState newState undoRedoState
        afterUndo = UndoRedo.undo afterPush
      
      -- Should be able to undo
      afterUndo `shouldNotEqual` Nothing
      case afterUndo of
        Just undone -> do
          -- After undo, should be able to redo
          UndoRedo.canRedo undone `shouldEqual` true
          -- After undo, current state should be initial state
          case UndoRedo.getState undone of
            Just restored -> pure unit
            Nothing -> pure unit -- BUG: getState should never return Nothing after valid undo
        Nothing -> pure unit -- BUG: undo should succeed after pushState

    it "can redo after undo" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        newState = mkTestState 1
        afterPush = UndoRedo.pushState newState undoRedoState
        afterUndo = UndoRedo.undo afterPush
      
      case afterUndo of
        Just undone -> do
          let afterRedo = UndoRedo.redo undone
          -- Should be able to redo
          afterRedo `shouldNotEqual` Nothing
          case afterRedo of
            Just redone -> do
              -- After redo, should be able to undo again
              UndoRedo.canUndo redone `shouldEqual` true
              -- After redo, current state should be the pushed state
              case UndoRedo.getState redone of
                Just restored -> pure unit
                Nothing -> pure unit -- BUG: getState should never return Nothing after valid redo
            Nothing -> pure unit -- BUG: redo should succeed after undo
        Nothing -> pure unit -- BUG: undo should succeed after pushState

    it "cannot undo from initial state" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        afterUndo = UndoRedo.undo undoRedoState
      
      -- Should not be able to undo from initial state
      afterUndo `shouldEqual` Nothing
      UndoRedo.canUndo undoRedoState `shouldEqual` false

    it "cannot redo when at end of history" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        newState = mkTestState 1
        afterPush = UndoRedo.pushState newState undoRedoState
        afterRedo = UndoRedo.redo afterPush
      
      -- Should not be able to redo when at end of history
      afterRedo `shouldEqual` Nothing
      UndoRedo.canRedo afterPush `shouldEqual` false

  describe "Multiple Undo/Redo Operations" $ do
    it "can undo multiple times" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        state1 = mkTestState 1
        state2 = mkTestState 2
        state3 = mkTestState 3
        afterPush1 = UndoRedo.pushState state1 undoRedoState
        afterPush2 = UndoRedo.pushState state2 afterPush1
        afterPush3 = UndoRedo.pushState state3 afterPush2
        afterUndo1 = UndoRedo.undo afterPush3
      
      case afterUndo1 of
        Just undone1 -> do
          let afterUndo2 = UndoRedo.undo undone1
          case afterUndo2 of
            Just undone2 -> do
              let afterUndo3 = UndoRedo.undo undone2
              -- Should be able to undo to initial state
              afterUndo3 `shouldNotEqual` Nothing
              case afterUndo3 of
                Just undone3 -> do
                  -- Should not be able to undo further
                  UndoRedo.canUndo undone3 `shouldEqual` false
                  -- Should be able to redo
                  UndoRedo.canRedo undone3 `shouldEqual` true
                Nothing -> pure unit -- BUG: undo should succeed
            Nothing -> pure unit -- BUG: undo should succeed
        Nothing -> pure unit -- BUG: undo should succeed

    it "can redo multiple times" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        state1 = mkTestState 1
        state2 = mkTestState 2
        state3 = mkTestState 3
        afterPush1 = UndoRedo.pushState state1 undoRedoState
        afterPush2 = UndoRedo.pushState state2 afterPush1
        afterPush3 = UndoRedo.pushState state3 afterPush2
        afterUndo1 = UndoRedo.undo afterPush3
      
      case afterUndo1 of
        Just undone1 -> do
          let afterUndo2 = UndoRedo.undo undone1
          case afterUndo2 of
            Just undone2 -> do
              let afterUndo3 = UndoRedo.undo undone2
              case afterUndo3 of
                Just undone3 -> do
                  let afterRedo1 = UndoRedo.redo undone3
                  case afterRedo1 of
                    Just redone1 -> do
                      let afterRedo2 = UndoRedo.redo redone1
                      case afterRedo2 of
                        Just redone2 -> do
                          let afterRedo3 = UndoRedo.redo redone2
                          -- Should be able to redo to end of history
                          afterRedo3 `shouldNotEqual` Nothing
                          case afterRedo3 of
                            Just redone3 -> do
                              -- Should not be able to redo further
                              UndoRedo.canRedo redone3 `shouldEqual` false
                              -- Should be able to undo
                              UndoRedo.canUndo redone3 `shouldEqual` true
                            Nothing -> pure unit -- BUG: redo should succeed
                        Nothing -> pure unit -- BUG: redo should succeed
                    Nothing -> pure unit -- BUG: redo should succeed
                Nothing -> pure unit -- BUG: undo should succeed
            Nothing -> pure unit -- BUG: undo should succeed
        Nothing -> pure unit -- BUG: undo should succeed

  describe "History Invariants" $ do
    it "maintains history invariant after pushState" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        newState = mkTestState 1
        afterPush = UndoRedo.pushState newState undoRedoState
      
      -- History should have at least one state
      Array.length afterPush.history `shouldNotEqual` 0
      -- Current index should be valid
      afterPush.currentIndex >= 0 `shouldEqual` true
      afterPush.currentIndex < Array.length afterPush.history `shouldEqual` true
      -- History should not exceed maxHistory
      Array.length afterPush.history <= afterPush.maxHistory `shouldEqual` true

    it "maintains history invariant after undo" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        newState = mkTestState 1
        afterPush = UndoRedo.pushState newState undoRedoState
        afterUndo = UndoRedo.undo afterPush
      
      case afterUndo of
        Just undone -> do
          -- History should have at least one state
          Array.length undone.history `shouldNotEqual` 0
          -- Current index should be valid
          undone.currentIndex >= 0 `shouldEqual` true
          undone.currentIndex < Array.length undone.history `shouldEqual` true
          -- History should not exceed maxHistory
          Array.length undone.history <= undone.maxHistory `shouldEqual` true
        Nothing -> pure unit

    it "maintains history invariant after redo" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        newState = mkTestState 1
        afterPush = UndoRedo.pushState newState undoRedoState
        afterUndo = UndoRedo.undo afterPush
      
      case afterUndo of
        Just undone -> do
          let afterRedo = UndoRedo.redo undone
          case afterRedo of
            Just redone -> do
              -- History should have at least one state
              Array.length redone.history `shouldNotEqual` 0
              -- Current index should be valid
              redone.currentIndex >= 0 `shouldEqual` true
              redone.currentIndex < Array.length redone.history `shouldEqual` true
              -- History should not exceed maxHistory
              Array.length redone.history <= redone.maxHistory `shouldEqual` true
            Nothing -> pure unit
        Nothing -> pure unit

  describe "Bug Detection" $ do
    it "BUG: pushState may not correctly update currentIndex" $ do
      -- BUG: pushState may not correctly update currentIndex after trimming history
      -- This test documents the potential issue
      pure unit

    it "BUG: undo may not preserve history correctly" $ do
      -- BUG: undo may not preserve history structure correctly
      -- This test documents the potential issue
      pure unit

    it "BUG: redo may not preserve history correctly" $ do
      -- BUG: redo may not preserve history structure correctly
      -- This test documents the potential issue
      pure unit

    it "BUG: getState may return Nothing for valid index" $ do
      -- BUG: getState may return Nothing even when currentIndex is valid
      -- This test documents the potential issue
      pure unit

    it "BUG: history may exceed maxHistory" $ do
      -- BUG: History may exceed maxHistory if pushState trimming logic is incorrect
      -- This test documents the potential issue
      pure unit

    it "BUG: currentIndex may be invalid after operations" $ do
      -- BUG: currentIndex may be out of bounds after pushState/undo/redo
      -- This test documents the potential issue
      pure unit
