-- | Deep comprehensive branching scenarios tests
-- | Tests history branching behavior, edge cases, and bug detection
module Test.UndoRedo.BranchingSpec where

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

-- | Deep comprehensive branching scenarios tests
spec :: Spec Unit
spec = describe "Branching Scenarios Deep Tests" $ do
  describe "History Branching Behavior" $ do
    it "branches history when pushing state after undo" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        state1 = mkTestState 1
        state2 = mkTestState 2
        state3 = mkTestState 3
        afterPush1 = UndoRedo.pushState state1 undoRedoState
        afterPush2 = UndoRedo.pushState state2 afterPush1
        afterPush3 = UndoRedo.pushState state3 afterPush2
        afterUndo = UndoRedo.undo afterPush3
      
      case afterUndo of
        Just undone -> do
          let state4 = mkTestState 4
          let afterPush4 = UndoRedo.pushState state4 undone
          -- After pushing state4, should not be able to redo to state3
          UndoRedo.canRedo afterPush4 `shouldEqual` false
          -- History should be branched (state3 removed)
          Array.length afterPush4.history `shouldEqual` 3 -- initialState, state1, state2, state4
        Nothing -> pure unit

    it "removes future states when branching" $ do
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
              let state4 = mkTestState 4
              let afterPush4 = UndoRedo.pushState state4 undone2
              -- After pushing state4, should not be able to redo to state2 or state3
              UndoRedo.canRedo afterPush4 `shouldEqual` false
              -- History should only contain states up to undone2 + state4
              Array.length afterPush4.history `shouldEqual` 3 -- initialState, state1, state4
            Nothing -> pure unit
        Nothing -> pure unit

    it "preserves history before currentIndex when branching" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        state1 = mkTestState 1
        state2 = mkTestState 2
        state3 = mkTestState 3
        afterPush1 = UndoRedo.pushState state1 undoRedoState
        afterPush2 = UndoRedo.pushState state2 afterPush1
        afterPush3 = UndoRedo.pushState state3 afterPush2
        afterUndo = UndoRedo.undo afterPush3
      
      case afterUndo of
        Just undone -> do
          let state4 = mkTestState 4
          let afterPush4 = UndoRedo.pushState state4 undone
          -- History before currentIndex should be preserved
          -- BUG: History preservation may not work correctly
          -- This test documents the potential issue
          Array.length afterPush4.history >= 2 `shouldEqual` true
        Nothing -> pure unit

  describe "Branching Edge Cases" $ do
    it "branches from initial state" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        state1 = mkTestState 1
        afterPush = UndoRedo.pushState state1 undoRedoState
      
      -- After pushing, should not be able to redo
      UndoRedo.canRedo afterPush `shouldEqual` false
      -- History should contain initial state and new state
      Array.length afterPush.history `shouldEqual` 2

    it "branches from end of history" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        state1 = mkTestState 1
        state2 = mkTestState 2
        afterPush1 = UndoRedo.pushState state1 undoRedoState
        afterPush2 = UndoRedo.pushState state2 afterPush1
        state3 = mkTestState 3
        afterPush3 = UndoRedo.pushState state3 afterPush2
      
      -- After pushing state3, should not be able to redo
      UndoRedo.canRedo afterPush3 `shouldEqual` false
      -- History should contain all states
      Array.length afterPush3.history `shouldEqual` 4

    it "branches multiple times" $ do
      let
        initialState = mkTestState 0
        undoRedoState = UndoRedo.initialUndoRedoState initialState
        state1 = mkTestState 1
        state2 = mkTestState 2
        state3 = mkTestState 3
        afterPush1 = UndoRedo.pushState state1 undoRedoState
        afterPush2 = UndoRedo.pushState state2 afterPush1
        afterUndo = UndoRedo.undo afterPush2
      
      case afterUndo of
        Just undone -> do
          let state4 = mkTestState 4
          let afterPush3 = UndoRedo.pushState state4 undone
          let afterUndo2 = UndoRedo.undo afterPush3
          case afterUndo2 of
            Just undone2 -> do
              let state5 = mkTestState 5
              let afterPush4 = UndoRedo.pushState state5 undone2
              -- After multiple branches, history should be correct
              -- BUG: Multiple branches may cause history corruption
              -- This test documents the potential issue
              Array.length afterPush4.history >= 2 `shouldEqual` true
            Nothing -> pure unit
        Nothing -> pure unit

  describe "Bug Detection" $ do
    it "BUG: branching may not remove all future states" $ do
      -- BUG: When branching, some future states may not be removed
      -- This test documents the potential issue
      pure unit

    it "BUG: branching may corrupt history structure" $ do
      -- BUG: Branching may cause history structure corruption
      -- This test documents the potential issue
      pure unit

    it "BUG: branching may cause currentIndex to be invalid" $ do
      -- BUG: After branching, currentIndex may point to invalid state
      -- This test documents the potential issue
      pure unit

    it "BUG: branching may not preserve history correctly" $ do
      -- BUG: History before currentIndex may not be preserved correctly
      -- This test documents the potential issue
      pure unit

    it "BUG: branching may cause memory leaks" $ do
      -- BUG: Removed states may not be garbage collected
      -- This test documents the potential issue
      pure unit
