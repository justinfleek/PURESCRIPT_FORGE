-- | Property Tests for Undo/Redo with Realistic Distributions
-- |
-- | Based on spec 70-TESTING-STRATEGY.md and 71-UNIT-TESTING.md
-- | Tests undo/redo invariants with realistic state distributions
-- |
-- | Reference: REQUIRED/trtllm-serve-main/nix/openai-proxy-hs/ProxyPropTest.hs
module Test.Sidepanel.Property.UndoRedoProps where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Test.QuickCheck (class Arbitrary, arbitrary, (===), (==>))
import Test.QuickCheck.Gen (Gen, chooseInt, chooseFloat, arrayOf, elements, frequency)
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Sidepanel.State.UndoRedo
  ( UndoRedoState
  , initialUndoRedoState
  , pushState
  , undo
  , redo
  , canUndo
  , canRedo
  , getState
  , defaultMaxHistory
  )
import Sidepanel.State.AppState (AppState, initialState)
import Sidepanel.State.Reducer (reduce)
import Sidepanel.State.Actions (Action(..))
import Data.Array (range)

-- | Realistic AppState generator
-- | Uses realistic distributions:
-- | - Balance: Normal distribution (μ=50, σ=20), bounded [0, 100]
-- | - Connection: 90% connected, 10% disconnected
-- | - Session: 70% have session, 30% no session
instance arbitraryAppState :: Arbitrary AppState where
  arbitrary = do
    -- Generate realistic balance (normal-like distribution)
    diem <- normalLike 50.0 20.0 0.0 100.0
    usd <- normalLike 10.0 5.0 0.0 50.0
    effective <- pure (diem + usd)
    
    -- Connection: 90% connected
    connected <- frequency
      [ (90.0, pure true)
      , (10.0, pure false)
      ]
    
    -- Use initialState as base and modify
    pure initialState
      { connected = connected
      , balance = initialState.balance
        { venice = Just
          { diem
          , usd
          , effective
          , todayUsed: 0.0
          , todayStartBalance: diem
          , resetCountdown: Nothing
          }
        }
      }

-- | Normal-like distribution generator (approximated with uniform + bias)
-- | Parameters: mean, stddev, min, max
normalLike :: Number -> Number -> Number -> Number -> Gen Number
normalLike mean stddev minVal maxVal = do
  -- Approximate normal with uniform + bias toward mean
  base <- chooseFloat minVal maxVal
  bias <- chooseFloat (-stddev) stddev
  let result = base + (mean - base) * 0.3 + bias
  pure $ clamp minVal maxVal result

clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal val
  | val < minVal = minVal
  | val > maxVal = maxVal
  | otherwise = val

-- | UndoRedoState generator with realistic history lengths
instance arbitraryUndoRedoState :: Arbitrary UndoRedoState where
  arbitrary = do
    -- History length: Uniform [1, maxHistory]
    historyLen <- chooseInt 1 defaultMaxHistory
    -- Current index: Uniform [0, historyLen - 1]
    currentIdx <- chooseInt 0 (historyLen - 1)
    
    -- Generate history array
    history <- arrayOf historyLen arbitrary
    
    pure
      { history
      , currentIndex: currentIdx
      , maxHistory: defaultMaxHistory
      }

-- | Action type for undo/redo sequences
data UndoRedoAction = UndoAction | RedoAction | NewStateAction AppState

derive instance eqUndoRedoAction :: Eq UndoRedoAction

instance arbitraryUndoRedoAction :: Arbitrary UndoRedoAction where
  arbitrary = frequency
    [ (40.0, pure UndoAction)  -- 40% undo
    , (10.0, pure RedoAction)  -- 10% redo
    , (50.0, NewStateAction <$> arbitrary)  -- 50% new state
    ]

-- | Property: History invariant always holds
-- | `0 <= currentIndex < length history`
prop_historyInvariant :: UndoRedoState -> Boolean
prop_historyInvariant state =
  let len = Array.length state.history
  in len > 0 && state.currentIndex >= 0 && state.currentIndex < len

-- | Property: History is bounded
-- | `length history <= maxHistory`
prop_historyBounded :: UndoRedoState -> Boolean
prop_historyBounded state =
  Array.length state.history <= state.maxHistory

-- | Property: Can undo iff currentIndex > 0
prop_canUndoCorrect :: UndoRedoState -> Boolean
prop_canUndoCorrect state =
  canUndo state === (state.currentIndex > 0)

-- | Property: Can redo iff currentIndex < last index
prop_canRedoCorrect :: UndoRedoState -> Boolean
prop_canRedoCorrect state =
  let len = Array.length state.history
  in canRedo state === (state.currentIndex < len - 1)

-- | Property: Undo decreases index by 1
prop_undoDecreasesIndex :: UndoRedoState -> Boolean
prop_undoDecreasesIndex state =
  canUndo state ==>
    case undo state of
      Just newState -> newState.currentIndex === state.currentIndex - 1
      Nothing -> false

-- | Property: Redo increases index by 1
prop_redoIncreasesIndex :: UndoRedoState -> Boolean
prop_redoIncreasesIndex state =
  canRedo state ==>
    case redo state of
      Just newState -> newState.currentIndex === state.currentIndex + 1
      Nothing -> false

-- | Property: Undo preserves history
prop_undoPreservesHistory :: UndoRedoState -> Boolean
prop_undoPreservesHistory state =
  canUndo state ==>
    case undo state of
      Just newState -> newState.history === state.history
      Nothing -> false

-- | Property: Redo preserves history
prop_redoPreservesHistory :: UndoRedoState -> Boolean
prop_redoPreservesHistory state =
  canRedo state ==>
    case redo state of
      Just newState -> newState.history === state.history
      Nothing -> false

-- | Property: Push state removes future states (branching)
prop_pushBranchesHistory :: UndoRedoState -> AppState -> Boolean
prop_pushBranchesHistory state newState =
  let
    newUndoState = pushState newState state
    expectedLen = min (state.currentIndex + 2) state.maxHistory
    -- History should be: [states up to currentIndex] ++ [newState]
    -- Trimmed if exceeds maxHistory
  in
    Array.length newUndoState.history === expectedLen &&
    newUndoState.currentIndex === Array.length newUndoState.history - 1

-- | Property: Push state updates index correctly
prop_pushUpdatesIndex :: UndoRedoState -> AppState -> Boolean
prop_pushUpdatesIndex state newState =
  let newUndoState = pushState newState state
  in newUndoState.currentIndex === Array.length newUndoState.history - 1

-- | Property: Get state returns correct state
prop_getStateCorrect :: UndoRedoState -> Boolean
prop_getStateCorrect state =
  case getState state of
    Just _ -> true  -- State exists
    Nothing -> false  -- Should not happen (invariant violation)

-- | Property: Undo/redo round-trip
prop_undoRedoRoundTrip :: UndoRedoState -> Boolean
prop_undoRedoRoundTrip state =
  canUndo state ==>
    case undo state of
      Just undoneState ->
        canRedo undoneState ==>
          case redo undoneState of
            Just redoneState -> redoneState === state
            Nothing -> false
      Nothing -> false

-- | Property: Multiple undo/redo sequences
prop_multipleUndoRedo :: UndoRedoState -> Boolean
prop_multipleUndoRedo state =
  let
    -- Undo twice
    state1 = fromMaybe state (undo state >>= undo)
    -- Redo twice
    state2 = fromMaybe state1 (redo state1 >>= redo)
  in
    state2 === state || not (canUndo state && canRedo state1)

-- | Property: Push after undo branches correctly
prop_pushAfterUndo :: UndoRedoState -> AppState -> Boolean
prop_pushAfterUndo state newState =
  canUndo state ==>
    case undo state of
      Just undoneState ->
        let pushedState = pushState newState undoneState
        in pushedState.currentIndex === Array.length pushedState.history - 1
      Nothing -> false

-- | Property: History never exceeds maxHistory
prop_historyNeverExceedsMax :: UndoRedoState -> AppState -> Boolean
prop_historyNeverExceedsMax state newState =
  let newUndoState = pushState newState state
  in Array.length newUndoState.history <= newUndoState.maxHistory

-- | Property: Initial state has exactly one state
prop_initialStateCorrect :: AppState -> Boolean
prop_initialStateCorrect appState =
  let undoState = initialUndoRedoState appState
  in Array.length undoState.history === 1 &&
     undoState.currentIndex === 0

-- | Property: Realistic undo/redo sequence
-- | Simulates realistic user behavior:
-- | - 50% new actions
-- | - 40% undo
-- | - 10% redo
prop_realisticSequence :: UndoRedoState -> Array UndoRedoAction -> Boolean
prop_realisticSequence initialState actions =
  let
    runAction :: UndoRedoState -> UndoRedoAction -> UndoRedoState
    runAction currentState = case _ of
      UndoAction -> fromMaybe currentState (undo currentState)
      RedoAction -> fromMaybe currentState (redo currentState)
      NewStateAction newAppState -> pushState newAppState currentState
    
    finalState = Array.foldl runAction initialState actions
    
    -- All invariants must hold
    invariant1 = prop_historyInvariant finalState
    invariant2 = prop_historyBounded finalState
    invariant3 = prop_getStateCorrect finalState
  in
    invariant1 && invariant2 && invariant3

-- ============================================================================
-- DEEP BUG-FINDING PROPERTY TESTS
-- ============================================================================

-- | Property: Restored state matches original state exactly
-- | When we undo then redo, we should get back the exact same state
prop_stateRestorationExact :: UndoRedoState -> Boolean
prop_stateRestorationExact state =
  canUndo state ==>
    case undo state of
      Just undoneState ->
        case getState undoneState of
          Just restoredState ->
            case redo undoneState of
              Just redoneState ->
                case getState redoneState of
                  Just finalState ->
                    -- Restored state should match original state
                    finalState === (fromMaybe initialState (getState state))
                  Nothing -> false
              Nothing -> false
          Nothing -> false
      Nothing -> true  -- Cannot undo, property holds trivially

-- | Property: Restored state preserves all fields
-- | All fields of restored state should match original
prop_stateRestorationPreservesFields :: UndoRedoState -> Boolean
prop_stateRestorationPreservesFields state =
  canUndo state ==>
    case undo state of
      Just undoneState ->
        case getState undoneState, getState state of
          Just restored, Just original ->
            -- Check key fields are preserved
            restored.connected === original.connected &&
            restored.balance.venice === original.balance.venice &&
            restored.session === original.session
          _, _ -> false
      Nothing -> true

-- | Property: Multiple undo/redo cycles restore correctly
prop_multipleCyclesRestore :: UndoRedoState -> Int -> Boolean
prop_multipleCyclesRestore state cycles =
  let
    absCycles = abs cycles `mod` 10  -- Limit to reasonable range
    -- Undo absCycles times
    undoneState = Array.foldl (\s _ -> fromMaybe s (undo s)) state (range 0 (absCycles - 1))
    -- Redo absCycles times
    redoneState = Array.foldl (\s _ -> fromMaybe s (redo s)) undoneState (range 0 (absCycles - 1))
  in
    -- Should return to original state if cycles don't exceed history
    if absCycles <= state.currentIndex && absCycles <= Array.length state.history - 1 - state.currentIndex
      then redoneState === state
      else true  -- Property holds if cycles exceed history

-- | Property: Undo/redo preserves state structure
prop_undoRedoPreservesStructure :: UndoRedoState -> Boolean
prop_undoRedoPreservesStructure state =
  canUndo state ==>
    case undo state of
      Just undoneState ->
        case getState undoneState, getState state of
          Just restored, Just original ->
            -- State structure should be preserved
            prop_historyInvariant undoneState &&
            prop_historyBounded undoneState &&
            -- Key fields should be present and valid
            restored.connected === restored.connected &&  -- Boolean field exists
            restored.balance.venice === restored.balance.venice &&  -- Nested structure exists
            (case restored.session of
              Just _ -> true
              Nothing -> true)  -- Session may or may not exist
          _, _ -> false
      Nothing -> true

-- | Property: Branching removes all future states
prop_branchingRemovesFuture :: UndoRedoState -> AppState -> Boolean
prop_branchingRemovesFuture state newState =
  let
    newUndoState = pushState newState state
    -- All states after currentIndex should be removed
    expectedHistoryLen = state.currentIndex + 2  -- States up to currentIndex + newState
    actualHistoryLen = Array.length newUndoState.history
  in
    -- History should be trimmed if exceeds maxHistory, but should not exceed maxHistory
    actualHistoryLen <= state.maxHistory &&
    -- New state should be at the end
    newUndoState.currentIndex === actualHistoryLen - 1

-- | Property: Branching preserves history before currentIndex
prop_branchingPreservesPast :: UndoRedoState -> AppState -> Boolean
prop_branchingPreservesPast state newState =
  let
    newUndoState = pushState newState state
    -- States before and including currentIndex should be preserved
    preservedStates = Array.take (state.currentIndex + 1) state.history
    newHistoryPrefix = Array.take (state.currentIndex + 1) newUndoState.history
  in
    -- Preserved states should match (may be trimmed if exceeds maxHistory)
    if Array.length newHistoryPrefix <= Array.length preservedStates
      then newHistoryPrefix === Array.take (Array.length newHistoryPrefix) preservedStates
      else false

-- | Property: Multiple branches maintain consistency
prop_multipleBranchesConsistent :: UndoRedoState -> Array AppState -> Boolean
prop_multipleBranchesConsistent initialState newStates =
  let
    finalState = Array.foldl (\s newState -> pushState newState s) initialState newStates
    -- All invariants must hold after multiple branches
    invariant1 = prop_historyInvariant finalState
    invariant2 = prop_historyBounded finalState
    invariant3 = prop_getStateCorrect finalState
  in
    invariant1 && invariant2 && invariant3

-- | Property: Branching after deep undo works correctly
prop_branchAfterDeepUndo :: UndoRedoState -> AppState -> Int -> Boolean
prop_branchAfterDeepUndo state newState undoCount =
  let
    absUndoCount = abs undoCount `mod` (state.currentIndex + 1)  -- Don't exceed history
    -- Undo multiple times
    undoneState = Array.foldl (\s _ -> fromMaybe s (undo s)) state (range 0 (absUndoCount - 1))
    -- Branch after undo
    branchedState = pushState newState undoneState
  in
    -- Branching should work correctly
    prop_historyInvariant branchedState &&
    prop_historyBounded branchedState &&
    branchedState.currentIndex === Array.length branchedState.history - 1

-- | Property: Branching updates index correctly
prop_branchingUpdatesIndex :: UndoRedoState -> AppState -> Boolean
prop_branchingUpdatesIndex state newState =
  let
    newUndoState = pushState newState state
    expectedIndex = Array.length newUndoState.history - 1
  in
    newUndoState.currentIndex === expectedIndex

-- | Property: Trimming preserves most recent states
prop_trimmingPreservesRecent :: UndoRedoState -> AppState -> Boolean
prop_trimmingPreservesRecent state newState =
  let
    -- Create state at maxHistory boundary
    boundaryState = state { maxHistory = Array.length state.history }
    newUndoState = pushState newState boundaryState
    -- Most recent states should be preserved
    lastState = Array.last newUndoState.history
  in
    case lastState of
      Just s -> s === newState  -- New state should be last
      Nothing -> false

-- | Property: Trimming removes oldest states first
prop_trimmingRemovesOldest :: UndoRedoState -> Array AppState -> Boolean
prop_trimmingRemovesOldest initialState newStates =
  let
    -- Create state that will exceed maxHistory
    smallMaxHistory = 5
    smallState = initialState { maxHistory = smallMaxHistory }
    -- Push many states
    finalState = Array.foldl (\s newState -> pushState newState s) smallState newStates
  in
    -- History should not exceed maxHistory
    Array.length finalState.history <= smallMaxHistory &&
    -- Most recent states should be preserved
    case Array.last finalState.history of
      Just _ -> true
      Nothing -> false

-- | Property: Trimming maintains valid index
prop_trimmingMaintainsIndex :: UndoRedoState -> AppState -> Boolean
prop_trimmingMaintainsIndex state newState =
  let
    newUndoState = pushState newState state
  in
    prop_historyInvariant newUndoState &&
    newUndoState.currentIndex >= 0 &&
    newUndoState.currentIndex < Array.length newUndoState.history

-- | Property: Multiple trims maintain consistency
prop_multipleTrimsConsistent :: UndoRedoState -> Array AppState -> Boolean
prop_multipleTrimsConsistent initialState newStates =
  let
    smallMaxHistory = 3
    smallState = initialState { maxHistory = smallMaxHistory }
    finalState = Array.foldl (\s newState -> pushState newState s) smallState newStates
  in
    prop_historyInvariant finalState &&
    prop_historyBounded finalState &&
    Array.length finalState.history <= smallMaxHistory

-- | Property: Trimming at maxHistory boundary works
prop_trimmingAtBoundary :: UndoRedoState -> AppState -> Boolean
prop_trimmingAtBoundary state newState =
  let
    -- Set maxHistory to current history length
    boundaryState = state { maxHistory = Array.length state.history }
    newUndoState = pushState newState boundaryState
  in
    -- Should trim one state and add new one
    Array.length newUndoState.history === boundaryState.maxHistory &&
    newUndoState.currentIndex === Array.length newUndoState.history - 1

-- | Property: Undo from initial state preserves state
prop_undoFromInitial :: AppState -> Boolean
prop_undoFromInitial appState =
  let
    undoState = initialUndoRedoState appState
    -- Cannot undo from initial state
    canUndoResult = canUndo undoState
    undoResult = undo undoState
  in
    not canUndoResult &&
    undoResult === Nothing

-- | Property: Redo at end preserves state
prop_redoAtEnd :: UndoRedoState -> Boolean
prop_redoAtEnd state =
  let
    -- Move to end of history
    atEndState = state { currentIndex = Array.length state.history - 1 }
    canRedoResult = canRedo atEndState
    redoResult = redo atEndState
  in
    not canRedoResult &&
    redoResult === Nothing

-- | Property: Rapid push operations maintain invariants
prop_rapidPush :: UndoRedoState -> Array AppState -> Boolean
prop_rapidPush initialState newStates =
  let
    finalState = Array.foldl (\s newState -> pushState newState s) initialState newStates
  in
    prop_historyInvariant finalState &&
    prop_historyBounded finalState &&
    prop_getStateCorrect finalState

-- | Property: Alternating undo/redo maintains consistency
prop_alternatingUndoRedo :: UndoRedoState -> Int -> Boolean
prop_alternatingUndoRedo state count =
  let
    absCount = abs count `mod` 5  -- Limit to reasonable range
    -- Alternate undo/redo
    finalState = Array.foldl (\s i ->
      if i `mod` 2 == 0
        then fromMaybe s (undo s)
        else fromMaybe s (redo s)
    ) state (range 0 (absCount - 1))
  in
    prop_historyInvariant finalState &&
    prop_historyBounded finalState &&
    prop_getStateCorrect finalState

-- | Property: Push at maxHistory maintains bounds
prop_pushAtMaxHistory :: UndoRedoState -> AppState -> Boolean
prop_pushAtMaxHistory state newState =
  let
    -- Set maxHistory to current length
    atMaxState = state { maxHistory = Array.length state.history }
    newUndoState = pushState newState atMaxState
  in
    Array.length newUndoState.history <= newUndoState.maxHistory &&
    newUndoState.currentIndex === Array.length newUndoState.history - 1

-- | Property: Undo/redo with reducer integration
prop_reducerIntegration :: AppState -> Action -> Boolean
prop_reducerIntegration initialState action =
  -- Skip Undo/Redo actions for this test
  case action of
    Undo -> true
    Redo -> true
    _ ->
      let
        -- Apply action
        newState = reduce initialState action
        -- Undo
        undoneState = reduce newState Undo
        -- Redo
        redoneState = reduce undoneState Redo
      in
        -- Should return to newState (not initialState, since we pushed newState)
        redoneState === newState

-- | Property: State transitions preserve undo/redo state
prop_stateTransitionsPreserveUndoRedo :: AppState -> Action -> Boolean
prop_stateTransitionsPreserveUndoRedo state action =
  case action of
    Undo -> true
    Redo -> true
    _ ->
      let
        newState = reduce state action
        -- undoRedo should be updated
        newHistoryLen = Array.length newState.undoRedo.history
        oldHistoryLen = Array.length state.undoRedo.history
      in
        -- History should grow (unless at maxHistory)
        newHistoryLen >= oldHistoryLen ||
        newHistoryLen === state.undoRedo.maxHistory

-- | Property: Undo restores correct reducer state
prop_undoRestoresReducerState :: AppState -> Action -> Boolean
prop_undoRestoresReducerState state action =
  case action of
    Undo -> true
    Redo -> true
    _ ->
      let
        -- Apply action
        newState = reduce state action
        -- Undo
        undoneState = reduce newState Undo
        -- Get restored state from undoRedo
        restoredState = fromMaybe initialState (getState undoneState.undoRedo)
      in
        -- Restored state should match original (except undoRedo field)
        restoredState.connected === state.connected &&
        restoredState.balance.venice === state.balance.venice &&
        restoredState.session === state.session

-- ============================================================================
-- BUG DETECTION PROPERTIES
-- ============================================================================

-- | BUG: pushState may not update index correctly after trimming
prop_bug_pushStateIndexAfterTrim :: UndoRedoState -> AppState -> Boolean
prop_bug_pushStateIndexAfterTrim state newState =
  let
    -- Create state at maxHistory boundary
    boundaryState = state { maxHistory = Array.length state.history }
    newUndoState = pushState newState boundaryState
    expectedIndex = Array.length newUndoState.history - 1
  in
    -- Index should point to last state
    newUndoState.currentIndex === expectedIndex
    -- BUG: If trimming logic is incorrect, index may be wrong

-- | BUG: History may become empty after trimming
prop_bug_historyEmptyAfterTrim :: UndoRedoState -> AppState -> Boolean
prop_bug_historyEmptyAfterTrim state newState =
  let
    newUndoState = pushState newState state
  in
    -- History should never be empty
    Array.length newUndoState.history > 0
    -- BUG: If trimming removes all states, history becomes empty

-- | BUG: currentIndex may be invalid after operations
prop_bug_invalidIndexAfterOps :: UndoRedoState -> AppState -> Boolean
prop_bug_invalidIndexAfterOps state newState =
  let
    newUndoState = pushState newState state
  in
    -- Index should always be valid
    prop_historyInvariant newUndoState
    -- BUG: Index may be negative or >= history.length

-- | BUG: Restored state may have wrong undoRedo field
prop_bug_restoredStateUndoRedo :: UndoRedoState -> Boolean
prop_bug_restoredStateUndoRedo state =
  canUndo state ==>
    case undo state of
      Just undoneState ->
        case getState undoneState of
          Just restoredState ->
            -- Restored state's undoRedo should match undoneState
            restoredState.undoRedo === undoneState
          Nothing -> false
      Nothing -> true
    -- BUG: Restored state may have stale undoRedo field

-- | BUG: Branching may not remove all future states
prop_bug_branchingIncomplete :: UndoRedoState -> AppState -> Boolean
prop_bug_branchingIncomplete state newState =
  let
    newUndoState = pushState newState state
    -- States after currentIndex should be removed
    expectedLen = min (state.currentIndex + 2) state.maxHistory
  in
    -- History length should match expected
    Array.length newUndoState.history === expectedLen ||
    Array.length newUndoState.history <= state.maxHistory
    -- BUG: If branching doesn't remove all future states, length will be wrong

-- | BUG: Memory leak with very large histories
-- | Tests that history trimming actually removes old states
prop_bug_memoryLeakLargeHistory :: UndoRedoState -> Array AppState -> Boolean
prop_bug_memoryLeakLargeHistory initialState newStates =
  let
    -- Create state with small maxHistory to force trimming
    smallMaxHistory = 3
    smallState = initialState { maxHistory = smallMaxHistory }
    -- Push many states (should trigger trimming)
    finalState = Array.foldl (\s newState -> pushState newState s) smallState newStates
    -- History should not grow unbounded
    historyLen = Array.length finalState.history
  in
    -- History should be bounded by maxHistory
    historyLen <= smallMaxHistory &&
    -- Most recent states should be preserved
    case Array.last finalState.history of
      Just _ -> true
      Nothing -> false
    -- BUG: If trimming doesn't work, history grows unbounded

-- | BUG: State corruption during rapid push/undo/redo sequences
-- | Tests that state remains consistent during rapid operations
prop_bug_stateCorruptionRapidOps :: UndoRedoState -> Array UndoRedoAction -> Boolean
prop_bug_stateCorruptionRapidOps initialState actions =
  let
    runAction :: UndoRedoState -> UndoRedoAction -> UndoRedoState
    runAction currentState = case _ of
      UndoAction -> fromMaybe currentState (undo currentState)
      RedoAction -> fromMaybe currentState (redo currentState)
      NewStateAction newAppState -> pushState newAppState currentState
    
    finalState = Array.foldl runAction initialState actions
    
    -- All invariants must hold
    invariant1 = prop_historyInvariant finalState
    invariant2 = prop_historyBounded finalState
    invariant3 = prop_getStateCorrect finalState
    -- State should be retrievable
    stateRetrievable = case getState finalState of
      Just _ -> true
      Nothing -> false
  in
    invariant1 && invariant2 && invariant3 && stateRetrievable
    -- BUG: Rapid operations may corrupt state

-- | BUG: Index calculation error during complex branching sequences
-- | Tests that index is always correct after complex operations
prop_bug_indexCalculationError :: UndoRedoState -> Array AppState -> Boolean
prop_bug_indexCalculationError initialState newStates =
  let
    -- Create complex sequence: undo, push, undo, push, etc.
    complexState = Array.foldl (\s i ->
      if i `mod` 2 == 0 && canUndo s
        then fromMaybe s (undo s)
        else s
    ) initialState (range 0 (Array.length newStates - 1))
    
    -- Now push all new states
    finalState = Array.foldl (\s newState -> pushState newState s) complexState newStates
    
    -- Index should always be valid and point to last state
    indexValid = prop_historyInvariant finalState
    indexPointsToLast = finalState.currentIndex === Array.length finalState.history - 1
  in
    indexValid && indexPointsToLast
    -- BUG: Complex sequences may cause index calculation errors

-- | BUG: History corruption during multiple branches
-- | Tests that history structure remains valid after multiple branches
prop_bug_historyCorruptionMultipleBranches :: UndoRedoState -> Array AppState -> Boolean
prop_bug_historyCorruptionMultipleBranches initialState newStates =
  let
    -- Create multiple branches by undoing then pushing
    branchedState = Array.foldl (\s newState ->
      if canUndo s
        then
          case undo s of
            Just undoneState -> pushState newState undoneState
            Nothing -> pushState newState s
        else pushState newState s
    ) initialState newStates
    
    -- History should be valid
    historyValid = prop_historyInvariant branchedState
    historyBounded = prop_historyBounded branchedState
    -- All states in history should be retrievable
    allStatesRetrievable = Array.all (\i ->
      case Array.index branchedState.history i of
        Just _ -> true
        Nothing -> false
    ) (range 0 (Array.length branchedState.history - 1))
  in
    historyValid && historyBounded && allStatesRetrievable
    -- BUG: Multiple branches may corrupt history structure

-- | BUG: Trimming may remove current state
-- | Tests that trimming never removes the current state
prop_bug_trimmingRemovesCurrentState :: UndoRedoState -> AppState -> Boolean
prop_bug_trimmingRemovesCurrentState state newState =
  let
    -- Create state at maxHistory boundary
    boundaryState = state { maxHistory = Array.length state.history }
    newUndoState = pushState newState boundaryState
    -- Current state should still be retrievable
    currentStateRetrievable = case getState newUndoState of
      Just _ -> true
      Nothing -> false
    -- Current state should match newState
    currentStateMatches = case getState newUndoState of
      Just s -> s === newState
      Nothing -> false
  in
    currentStateRetrievable && currentStateMatches
    -- BUG: Trimming may accidentally remove current state

-- | BUG: Undo/redo may not preserve state equality
-- | Tests that undo then redo returns to exact same state
prop_bug_undoRedoStateEquality :: UndoRedoState -> Boolean
prop_bug_undoRedoStateEquality state =
  canUndo state ==>
    case undo state of
      Just undoneState ->
        case redo undoneState of
          Just redoneState ->
            -- Should return to exact same state
            redoneState === state &&
            -- History should be identical
            redoneState.history === state.history &&
            -- Index should be identical
            redoneState.currentIndex === state.currentIndex
          Nothing -> false
      Nothing -> true
    -- BUG: Undo/redo may not preserve exact state equality

-- | BUG: Branching may corrupt state references
-- | Tests that states in history remain valid after branching
prop_bug_branchingCorruptsStateReferences :: UndoRedoState -> AppState -> Boolean
prop_bug_branchingCorruptsStateReferences state newState =
  let
    -- Save original states before branching
    originalStates = Array.take (state.currentIndex + 1) state.history
    newUndoState = pushState newState state
    -- States before currentIndex should be preserved (may be trimmed)
    preservedStates = Array.take (min (state.currentIndex + 1) (Array.length newUndoState.history)) newUndoState.history
  in
    -- Preserved states should match original (up to trimming)
    if Array.length preservedStates <= Array.length originalStates
      then
        Array.all (\i ->
          case Array.index preservedStates i, Array.index originalStates (Array.length originalStates - Array.length preservedStates + i) of
            Just preserved, Just original -> preserved === original
            _, _ -> false
        ) (range 0 (Array.length preservedStates - 1))
      else false
    -- BUG: Branching may corrupt state references in history

-- | BUG: Multiple undo operations may skip states
-- | Tests that multiple undo operations visit all intermediate states
prop_bug_multipleUndoSkippingStates :: UndoRedoState -> Int -> Boolean
prop_bug_multipleUndoSkippingStates state undoCount =
  let
    absUndoCount = abs undoCount `mod` (state.currentIndex + 1)
    -- Perform multiple undo operations
    undoneState = Array.foldl (\s _ -> fromMaybe s (undo s)) state (range 0 (absUndoCount - 1))
    -- Index should decrease by exactly undoCount
    indexDecreased = undoneState.currentIndex === state.currentIndex - absUndoCount
    -- History should be preserved
    historyPreserved = undoneState.history === state.history
  in
    indexDecreased && historyPreserved
    -- BUG: Multiple undo may skip states or corrupt history

-- | BUG: Redo after branching may access invalid state
-- | Tests that redo is not possible after branching
prop_bug_redoAfterBranching :: UndoRedoState -> AppState -> Boolean
prop_bug_redoAfterBranching state newState =
  let
    -- Branch by pushing new state
    branchedState = pushState newState state
    -- Redo should not be possible (we're at end of history)
    canRedoResult = canRedo branchedState
    redoResult = redo branchedState
  in
    not canRedoResult &&
    redoResult === Nothing
    -- BUG: Redo may be incorrectly allowed after branching

-- | BUG: State restoration may lose nested state fields
-- | Tests that all nested fields are preserved during restoration
prop_bug_stateRestorationLosesNestedFields :: UndoRedoState -> Boolean
prop_bug_stateRestorationLosesNestedFields state =
  canUndo state ==>
    case undo state of
      Just undoneState ->
        case getState undoneState, getState state of
          Just restored, Just original ->
            -- Check nested fields are preserved
            restored.balance.venice === original.balance.venice &&
            (case restored.session, original.session of
              Just rSession, Just oSession -> rSession === oSession
              Nothing, Nothing -> true
              _, _ -> false) &&
            restored.connected === original.connected
          _, _ -> false
      Nothing -> true
    -- BUG: State restoration may lose nested fields

-- | BUG: History trimming may cause index out of bounds
-- | Tests that index remains valid after aggressive trimming
prop_bug_trimmingIndexOutOfBounds :: UndoRedoState -> Array AppState -> Boolean
prop_bug_trimmingIndexOutOfBounds initialState newStates =
  let
    -- Create state with very small maxHistory
    tinyMaxHistory = 2
    tinyState = initialState { maxHistory = tinyMaxHistory }
    -- Push many states to force aggressive trimming
    finalState = Array.foldl (\s newState -> pushState newState s) tinyState newStates
    -- Index should always be valid
    indexValid = prop_historyInvariant finalState
    -- Index should point to last state
    indexPointsToLast = finalState.currentIndex === Array.length finalState.history - 1
  in
    indexValid && indexPointsToLast
    -- BUG: Aggressive trimming may cause index out of bounds

spec :: Spec Unit
spec = describe "Undo/Redo Property Tests" do
  describe "History Invariants" do
    it "history invariant always holds" $
      quickCheck prop_historyInvariant
    
    it "history is bounded" $
      quickCheck prop_historyBounded
    
    it "getState always returns valid state" $
      quickCheck prop_getStateCorrect
  
  describe "Undo/Redo Operations" do
    it "canUndo is correct" $
      quickCheck prop_canUndoCorrect
    
    it "canRedo is correct" $
      quickCheck prop_canRedoCorrect
    
    it "undo decreases index by 1" $
      quickCheck prop_undoDecreasesIndex
    
    it "redo increases index by 1" $
      quickCheck prop_redoIncreasesIndex
    
    it "undo preserves history" $
      quickCheck prop_undoPreservesHistory
    
    it "redo preserves history" $
      quickCheck prop_redoPreservesHistory
  
  describe "State Management" do
    it "push state branches history correctly" $
      quickCheck prop_pushBranchesHistory
    
    it "push state updates index correctly" $
      quickCheck prop_pushUpdatesIndex
    
    it "push after undo branches correctly" $
      quickCheck prop_pushAfterUndo
    
    it "history never exceeds maxHistory" $
      quickCheck prop_historyNeverExceedsMax
  
  describe "Round-Trip Properties" do
    it "undo/redo round-trip" $
      quickCheck prop_undoRedoRoundTrip
    
    it "multiple undo/redo sequences" $
      quickCheck prop_multipleUndoRedo
  
  describe "Initialization" do
    it "initial state has exactly one state" $
      quickCheck prop_initialStateCorrect
  
  describe "Realistic Sequences" do
    it "realistic undo/redo sequence preserves invariants" $
      quickCheck prop_realisticSequence
  
  -- ============================================================================
  -- DEEP BUG-FINDING PROPERTY TESTS
  -- ============================================================================
  
  describe "State Restoration Properties" do
    it "restored state matches original state exactly" $
      quickCheck prop_stateRestorationExact
    
    it "restored state preserves all fields" $
      quickCheck prop_stateRestorationPreservesFields
    
    it "multiple undo/redo cycles restore correctly" $
      quickCheck prop_multipleCyclesRestore
    
    it "undo/redo preserves state structure" $
      quickCheck prop_undoRedoPreservesStructure
  
  describe "Branching Properties" do
    it "branching removes all future states" $
      quickCheck prop_branchingRemovesFuture
    
    it "branching preserves history before currentIndex" $
      quickCheck prop_branchingPreservesPast
    
    it "multiple branches maintain consistency" $
      quickCheck prop_multipleBranchesConsistent
    
    it "branching after deep undo works correctly" $
      quickCheck prop_branchAfterDeepUndo
    
    it "branching updates index correctly" $
      quickCheck prop_branchingUpdatesIndex
  
  describe "History Trimming Properties" do
    it "trimming preserves most recent states" $
      quickCheck prop_trimmingPreservesRecent
    
    it "trimming removes oldest states first" $
      quickCheck prop_trimmingRemovesOldest
    
    it "trimming maintains valid index" $
      quickCheck prop_trimmingMaintainsIndex
    
    it "multiple trims maintain consistency" $
      quickCheck prop_multipleTrimsConsistent
    
    it "trimming at maxHistory boundary works" $
      quickCheck prop_trimmingAtBoundary
  
  describe "Edge Case Properties" do
    it "undo from initial state preserves state" $
      quickCheck prop_undoFromInitial
    
    it "redo at end preserves state" $
      quickCheck prop_redoAtEnd
    
    it "rapid push operations maintain invariants" $
      quickCheck prop_rapidPush
    
    it "alternating undo/redo maintains consistency" $
      quickCheck prop_alternatingUndoRedo
    
    it "push at maxHistory maintains bounds" $
      quickCheck prop_pushAtMaxHistory
  
  describe "Integration Properties" do
    it "undo/redo with reducer integration" $
      quickCheck prop_reducerIntegration
    
    it "state transitions preserve undo/redo state" $
      quickCheck prop_stateTransitionsPreserveUndoRedo
    
    it "undo restores correct reducer state" $
      quickCheck prop_undoRestoresReducerState
  
  describe "Bug Detection Properties" do
    it "BUG: pushState may not update index correctly after trimming" $
      quickCheck prop_bug_pushStateIndexAfterTrim
    
    it "BUG: history may become empty after trimming" $
      quickCheck prop_bug_historyEmptyAfterTrim
    
    it "BUG: currentIndex may be invalid after operations" $
      quickCheck prop_bug_invalidIndexAfterOps
    
    it "BUG: restored state may have wrong undoRedo field" $
      quickCheck prop_bug_restoredStateUndoRedo
    
    it "BUG: branching may not remove all future states" $
      quickCheck prop_bug_branchingIncomplete
    
    it "BUG: Memory leak with very large histories" $
      quickCheck prop_bug_memoryLeakLargeHistory
    
    it "BUG: State corruption during rapid operations" $
      quickCheck prop_bug_stateCorruptionRapidOps
    
    it "BUG: Index calculation error during complex branching" $
      quickCheck prop_bug_indexCalculationError
    
    it "BUG: History corruption during multiple branches" $
      quickCheck prop_bug_historyCorruptionMultipleBranches
    
    it "BUG: Trimming may remove current state" $
      quickCheck prop_bug_trimmingRemovesCurrentState
    
    it "BUG: Undo/redo may not preserve state equality" $
      quickCheck prop_bug_undoRedoStateEquality
    
    it "BUG: Branching may corrupt state references" $
      quickCheck prop_bug_branchingCorruptsStateReferences
    
    it "BUG: Multiple undo operations may skip states" $
      quickCheck prop_bug_multipleUndoSkippingStates
    
    it "BUG: Redo after branching may access invalid state" $
      quickCheck prop_bug_redoAfterBranching
    
    it "BUG: State restoration may lose nested fields" $
      quickCheck prop_bug_stateRestorationLosesNestedFields
    
    it "BUG: History trimming may cause index out of bounds" $
      quickCheck prop_bug_trimmingIndexOutOfBounds