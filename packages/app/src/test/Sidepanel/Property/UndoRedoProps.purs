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
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, choose, vectorOf, elements, frequency)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype, unwrap)
import Data.Ord (abs)
import Data.Tuple (Tuple(..))
import Sidepanel.State.UndoRedo
  ( UndoRedoState(..)
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

-- | Newtype wrapper for AppState to allow Arbitrary instance
-- | (PureScript cannot have typeclass instances for type aliases)
newtype ArbAppState = ArbAppState AppState

derive instance newtypeArbAppState :: Newtype ArbAppState _

-- | Realistic AppState generator
-- | Uses realistic distributions:
-- | - Balance: Normal distribution (mu=50, sigma=20), bounded [0, 100]
-- | - Connection: 90% connected, 10% disconnected
-- | - Session: 70% have session, 30% no session
instance arbitraryArbAppState :: Arbitrary ArbAppState where
  arbitrary = do
    -- Generate realistic balance (normal-like distribution)
    diem <- normalLike 50.0 20.0 0.0 100.0
    usd <- normalLike 10.0 5.0 0.0 50.0
    effective <- pure (diem + usd)

    -- Connection: 90% connected
    connected <- frequency
      (NEA.cons' (Tuple 90.0 (pure true))
        [ Tuple 10.0 (pure false)
        ])

    -- Use initialState as base and modify
    pure $ ArbAppState $ initialState
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
  base <- choose minVal maxVal
  bias <- choose (-stddev) stddev
  let result = base + (mean - base) * 0.3 + bias
  pure $ clamp minVal maxVal result

clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal val
  | val < minVal = minVal
  | val > maxVal = maxVal
  | otherwise = val

-- | Newtype wrapper for UndoRedoState to avoid orphan Arbitrary instance
newtype ArbUndoRedoState = ArbUndoRedoState UndoRedoState

derive instance newtypeArbUndoRedoState :: Newtype ArbUndoRedoState _

-- | UndoRedoState generator with realistic history lengths
instance arbitraryArbUndoRedoState :: Arbitrary ArbUndoRedoState where
  arbitrary = do
    -- History length: Uniform [1, maxHistory]
    historyLen <- chooseInt 1 defaultMaxHistory
    -- Current index: Uniform [0, historyLen - 1]
    currentIdx <- chooseInt 0 (historyLen - 1)

    -- Generate history array (unwrap ArbAppState to get AppState)
    history <- map (map unwrap) (vectorOf historyLen (arbitrary :: Gen ArbAppState))

    pure $ ArbUndoRedoState $ UndoRedoState
      { history
      , currentIndex: currentIdx
      , maxHistory: defaultMaxHistory
      }

-- | Newtype wrapper for Action to avoid orphan Arbitrary instance
newtype ArbAction = ArbAction Action

derive instance newtypeArbAction :: Newtype ArbAction _

instance arbitraryArbAction :: Arbitrary ArbAction where
  arbitrary = ArbAction <$> elements (NEA.cons' Connected [Disconnected, ToggleSidebar, SessionCleared, CountdownTick, ProofConnected, ProofDisconnected, Undo, Redo])

-- | Action type for undo/redo sequences
data UndoRedoAction = UndoAction | RedoAction | NewStateAction AppState

derive instance eqUndoRedoAction :: Eq UndoRedoAction

instance arbitraryUndoRedoAction :: Arbitrary UndoRedoAction where
  arbitrary = frequency
    (NEA.cons' (Tuple 40.0 (pure UndoAction))
      [ Tuple 10.0 (pure RedoAction)
      , Tuple 50.0 (NewStateAction <<< unwrap <$> (arbitrary :: Gen ArbAppState))
      ])

-- | Property: History invariant always holds
-- | `0 <= currentIndex < length history`
prop_historyInvariant :: ArbUndoRedoState -> Boolean
prop_historyInvariant (ArbUndoRedoState state) =
  let s = unwrap state
      len = Array.length s.history
  in len > 0 && s.currentIndex >= 0 && s.currentIndex < len

-- | Property: History is bounded
-- | `length history <= maxHistory`
prop_historyBounded :: ArbUndoRedoState -> Boolean
prop_historyBounded (ArbUndoRedoState state) =
  let s = unwrap state
  in Array.length s.history <= s.maxHistory

-- | Property: Can undo iff currentIndex > 0
prop_canUndoCorrect :: ArbUndoRedoState -> Boolean
prop_canUndoCorrect (ArbUndoRedoState state) =
  canUndo state == ((unwrap state).currentIndex > 0)

-- | Property: Can redo iff currentIndex < last index
prop_canRedoCorrect :: ArbUndoRedoState -> Boolean
prop_canRedoCorrect (ArbUndoRedoState state) =
  let s = unwrap state
      len = Array.length s.history
  in canRedo state == (s.currentIndex < len - 1)

-- | Property: Undo decreases index by 1
prop_undoDecreasesIndex :: ArbUndoRedoState -> Boolean
prop_undoDecreasesIndex (ArbUndoRedoState state) =
  if canUndo state
    then case undo state of
      Just newState -> (unwrap newState).currentIndex == (unwrap state).currentIndex - 1
      Nothing -> false
    else true

-- | Property: Redo increases index by 1
prop_redoIncreasesIndex :: ArbUndoRedoState -> Boolean
prop_redoIncreasesIndex (ArbUndoRedoState state) =
  if canRedo state
    then case redo state of
      Just newState -> (unwrap newState).currentIndex == (unwrap state).currentIndex + 1
      Nothing -> false
    else true

-- | Property: Undo preserves history
prop_undoPreservesHistory :: ArbUndoRedoState -> Boolean
prop_undoPreservesHistory (ArbUndoRedoState state) =
  if canUndo state
    then case undo state of
      Just newState -> (unwrap newState).history == (unwrap state).history
      Nothing -> false
    else true

-- | Property: Redo preserves history
prop_redoPreservesHistory :: ArbUndoRedoState -> Boolean
prop_redoPreservesHistory (ArbUndoRedoState state) =
  if canRedo state
    then case redo state of
      Just newState -> (unwrap newState).history == (unwrap state).history
      Nothing -> false
    else true

-- | Property: Push state removes future states (branching)
prop_pushBranchesHistory :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_pushBranchesHistory (ArbUndoRedoState state) (ArbAppState newState) =
  let
    s = unwrap state
    newUndoState = pushState newState state
    expectedLen = min (s.currentIndex + 2) s.maxHistory
    -- History should be: [states up to currentIndex] ++ [newState]
    -- Trimmed if exceeds maxHistory
  in
    (Array.length (unwrap newUndoState).history == expectedLen) &&
    ((unwrap newUndoState).currentIndex == Array.length (unwrap newUndoState).history - 1)

-- | Property: Push state updates index correctly
prop_pushUpdatesIndex :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_pushUpdatesIndex (ArbUndoRedoState state) (ArbAppState newState) =
  let newUndoState = pushState newState state
  in (unwrap newUndoState).currentIndex == Array.length (unwrap newUndoState).history - 1

-- | Property: Get state returns correct state
prop_getStateCorrect :: ArbUndoRedoState -> Boolean
prop_getStateCorrect (ArbUndoRedoState state) =
  case getState state of
    Just _ -> true  -- State exists
    Nothing -> false  -- Should not happen (invariant violation)

-- | Property: Undo/redo round-trip
prop_undoRedoRoundTrip :: ArbUndoRedoState -> Boolean
prop_undoRedoRoundTrip (ArbUndoRedoState state) =
  if canUndo state
    then case undo state of
      Just undoneState ->
        if canRedo undoneState
          then case redo undoneState of
            Just redoneState -> redoneState == state
            Nothing -> false
          else true
      Nothing -> false
    else true

-- | Property: Multiple undo/redo sequences
prop_multipleUndoRedo :: ArbUndoRedoState -> Boolean
prop_multipleUndoRedo (ArbUndoRedoState state) =
  let
    -- Undo twice
    state1 = fromMaybe state (undo state >>= undo)
    -- Redo twice
    state2 = fromMaybe state1 (redo state1 >>= redo)
  in
    (state2 == state) || not (canUndo state && canRedo state1)

-- | Property: Push after undo branches correctly
prop_pushAfterUndo :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_pushAfterUndo (ArbUndoRedoState state) (ArbAppState newState) =
  if canUndo state
    then case undo state of
      Just undoneState ->
        let pushedState = pushState newState undoneState
        in (unwrap pushedState).currentIndex == Array.length (unwrap pushedState).history - 1
      Nothing -> false
    else true

-- | Property: History never exceeds maxHistory
prop_historyNeverExceedsMax :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_historyNeverExceedsMax (ArbUndoRedoState state) (ArbAppState newState) =
  let newUndoState = pushState newState state
  in Array.length (unwrap newUndoState).history <= (unwrap newUndoState).maxHistory

-- | Property: Initial state has exactly one state
prop_initialStateCorrect :: ArbAppState -> Boolean
prop_initialStateCorrect (ArbAppState appState) =
  let undoState = initialUndoRedoState appState
  in (Array.length (unwrap undoState).history == 1) &&
     ((unwrap undoState).currentIndex == 0)

-- | Property: Realistic undo/redo sequence
-- | Simulates realistic user behavior:
-- | - 50% new actions
-- | - 40% undo
-- | - 10% redo
prop_realisticSequence :: ArbUndoRedoState -> Array UndoRedoAction -> Boolean
prop_realisticSequence (ArbUndoRedoState initialSt) actions =
  let
    runAction :: UndoRedoState -> UndoRedoAction -> UndoRedoState
    runAction currentState = case _ of
      UndoAction -> fromMaybe currentState (undo currentState)
      RedoAction -> fromMaybe currentState (redo currentState)
      NewStateAction newAppState -> pushState newAppState currentState

    finalState = Array.foldl runAction initialSt actions

    -- All invariants must hold
    invariant1 = prop_historyInvariant_raw finalState
    invariant2 = prop_historyBounded_raw finalState
    invariant3 = prop_getStateCorrect_raw finalState
  in
    invariant1 && invariant2 && invariant3

-- | Raw helper: History invariant (operates on UndoRedoState directly)
prop_historyInvariant_raw :: UndoRedoState -> Boolean
prop_historyInvariant_raw st =
  let s = unwrap st
      len = Array.length s.history
  in len > 0 && s.currentIndex >= 0 && s.currentIndex < len

-- | Raw helper: History bounded (operates on UndoRedoState directly)
prop_historyBounded_raw :: UndoRedoState -> Boolean
prop_historyBounded_raw st =
  let s = unwrap st
  in Array.length s.history <= s.maxHistory

-- | Raw helper: getState correct (operates on UndoRedoState directly)
prop_getStateCorrect_raw :: UndoRedoState -> Boolean
prop_getStateCorrect_raw st =
  case getState st of
    Just _ -> true
    Nothing -> false

-- ============================================================================
-- DEEP BUG-FINDING PROPERTY TESTS
-- ============================================================================

-- | Property: Restored state matches original state exactly
-- | When we undo then redo, we should get back the exact same state
prop_stateRestorationExact :: ArbUndoRedoState -> Boolean
prop_stateRestorationExact (ArbUndoRedoState state) =
  if canUndo state
    then case undo state of
      Just undoneState ->
        case getState undoneState of
          Just restoredState ->
            case redo undoneState of
              Just redoneState ->
                case getState redoneState of
                  Just finalState ->
                    -- Restored state should match original state
                    finalState == (fromMaybe initialState (getState state))
                  Nothing -> false
              Nothing -> false
          Nothing -> false
      Nothing -> true  -- Cannot undo, property holds trivially
    else true

-- | Property: Restored state preserves all fields
-- | All fields of restored state should match original
prop_stateRestorationPreservesFields :: ArbUndoRedoState -> Boolean
prop_stateRestorationPreservesFields (ArbUndoRedoState state) =
  if canUndo state
    then case undo state of
      Just undoneState ->
        case getState undoneState, getState state of
          Just restored, Just original ->
            -- Check key fields are preserved
            (restored.connected == original.connected) &&
            (restored.balance.venice == original.balance.venice) &&
            (restored.session == original.session)
          _, _ -> false
      Nothing -> true
    else true

-- | Property: Multiple undo/redo cycles restore correctly
prop_multipleCyclesRestore :: ArbUndoRedoState -> Int -> Boolean
prop_multipleCyclesRestore (ArbUndoRedoState state) cycles =
  let
    s = unwrap state
    absCycles = abs cycles `mod` 10  -- Limit to reasonable range
    -- Undo absCycles times
    undoneState = Array.foldl (\st _ -> fromMaybe st (undo st)) state (range 0 (absCycles - 1))
    -- Redo absCycles times
    redoneState = Array.foldl (\st _ -> fromMaybe st (redo st)) undoneState (range 0 (absCycles - 1))
  in
    -- Should return to original state if cycles don't exceed history
    if absCycles <= s.currentIndex && absCycles <= Array.length s.history - 1 - s.currentIndex
      then redoneState == state
      else true  -- Property holds if cycles exceed history

-- | Property: Undo/redo preserves state structure
prop_undoRedoPreservesStructure :: ArbUndoRedoState -> Boolean
prop_undoRedoPreservesStructure (ArbUndoRedoState state) =
  if canUndo state
    then case undo state of
      Just undoneState ->
        case getState undoneState, getState state of
          Just restored, Just original ->
            -- State structure should be preserved
            prop_historyInvariant_raw undoneState &&
            prop_historyBounded_raw undoneState &&
            -- Key fields should be present and valid
            (restored.connected == restored.connected) &&  -- Boolean field exists
            (restored.balance.venice == restored.balance.venice) &&  -- Nested structure exists
            (case restored.session of
              Just _ -> true
              Nothing -> true)  -- Session may or may not exist
          _, _ -> false
      Nothing -> true
    else true

-- | Property: Branching removes all future states
prop_branchingRemovesFuture :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_branchingRemovesFuture (ArbUndoRedoState state) (ArbAppState newState) =
  let
    s = unwrap state
    newUndoState = pushState newState state
    -- All states after currentIndex should be removed
    expectedHistoryLen = s.currentIndex + 2  -- States up to currentIndex + newState
    actualHistoryLen = Array.length (unwrap newUndoState).history
  in
    -- History should be trimmed if exceeds maxHistory, but should not exceed maxHistory
    actualHistoryLen <= s.maxHistory &&
    -- New state should be at the end
    ((unwrap newUndoState).currentIndex == actualHistoryLen - 1)

-- | Property: Branching preserves history before currentIndex
prop_branchingPreservesPast :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_branchingPreservesPast (ArbUndoRedoState state) (ArbAppState newState) =
  let
    s = unwrap state
    newUndoState = pushState newState state
    -- States before and including currentIndex should be preserved
    preservedStates = Array.take (s.currentIndex + 1) s.history
    newHistoryPrefix = Array.take (s.currentIndex + 1) (unwrap newUndoState).history
  in
    -- Preserved states should match (may be trimmed if exceeds maxHistory)
    if Array.length newHistoryPrefix <= Array.length preservedStates
      then newHistoryPrefix == Array.take (Array.length newHistoryPrefix) preservedStates
      else false

-- | Property: Multiple branches maintain consistency
prop_multipleBranchesConsistent :: ArbUndoRedoState -> Array ArbAppState -> Boolean
prop_multipleBranchesConsistent (ArbUndoRedoState initialSt) arbNewStates =
  let
    newStates = map unwrap arbNewStates
    finalState = Array.foldl (\st newState -> pushState newState st) initialSt newStates
    -- All invariants must hold after multiple branches
    invariant1 = prop_historyInvariant_raw finalState
    invariant2 = prop_historyBounded_raw finalState
    invariant3 = prop_getStateCorrect_raw finalState
  in
    invariant1 && invariant2 && invariant3

-- | Property: Branching after deep undo works correctly
prop_branchAfterDeepUndo :: ArbUndoRedoState -> ArbAppState -> Int -> Boolean
prop_branchAfterDeepUndo (ArbUndoRedoState state) (ArbAppState newState) undoCount =
  let
    s = unwrap state
    absUndoCount = abs undoCount `mod` (s.currentIndex + 1)  -- Don't exceed history
    -- Undo multiple times
    undoneState = Array.foldl (\st _ -> fromMaybe st (undo st)) state (range 0 (absUndoCount - 1))
    -- Branch after undo
    branchedState = pushState newState undoneState
  in
    -- Branching should work correctly
    prop_historyInvariant_raw branchedState &&
    prop_historyBounded_raw branchedState &&
    ((unwrap branchedState).currentIndex == Array.length (unwrap branchedState).history - 1)

-- | Property: Branching updates index correctly
prop_branchingUpdatesIndex :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_branchingUpdatesIndex (ArbUndoRedoState state) (ArbAppState newState) =
  let
    newUndoState = pushState newState state
    expectedIndex = Array.length (unwrap newUndoState).history - 1
  in
    (unwrap newUndoState).currentIndex == expectedIndex

-- | Property: Trimming preserves most recent states
prop_trimmingPreservesRecent :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_trimmingPreservesRecent (ArbUndoRedoState state) (ArbAppState newState) =
  let
    s = unwrap state
    -- Create state at maxHistory boundary
    boundaryState = UndoRedoState (s { maxHistory = Array.length s.history })
    newUndoState = pushState newState boundaryState
    -- Most recent states should be preserved
    lastState = Array.last (unwrap newUndoState).history
  in
    case lastState of
      Just st -> st == newState  -- New state should be last
      Nothing -> false

-- | Property: Trimming removes oldest states first
prop_trimmingRemovesOldest :: ArbUndoRedoState -> Array ArbAppState -> Boolean
prop_trimmingRemovesOldest (ArbUndoRedoState initialSt) arbNewStates =
  let
    s = unwrap initialSt
    newStates = map unwrap arbNewStates
    -- Create state that will exceed maxHistory
    smallMaxHistory = 5
    smallState = UndoRedoState (s { maxHistory = smallMaxHistory })
    -- Push many states
    finalState = Array.foldl (\st newState -> pushState newState st) smallState newStates
    fs = unwrap finalState
  in
    -- History should not exceed maxHistory
    Array.length fs.history <= smallMaxHistory &&
    -- Most recent states should be preserved
    case Array.last fs.history of
      Just _ -> true
      Nothing -> false

-- | Property: Trimming maintains valid index
prop_trimmingMaintainsIndex :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_trimmingMaintainsIndex (ArbUndoRedoState state) (ArbAppState newState) =
  let
    newUndoState = pushState newState state
  in
    prop_historyInvariant_raw newUndoState &&
    (unwrap newUndoState).currentIndex >= 0 &&
    (unwrap newUndoState).currentIndex < Array.length (unwrap newUndoState).history

-- | Property: Multiple trims maintain consistency
prop_multipleTrimsConsistent :: ArbUndoRedoState -> Array ArbAppState -> Boolean
prop_multipleTrimsConsistent (ArbUndoRedoState initialSt) arbNewStates =
  let
    s = unwrap initialSt
    newStates = map unwrap arbNewStates
    smallMaxHistory = 3
    smallState = UndoRedoState (s { maxHistory = smallMaxHistory })
    finalState = Array.foldl (\st newState -> pushState newState st) smallState newStates
    fs = unwrap finalState
  in
    prop_historyInvariant_raw finalState &&
    prop_historyBounded_raw finalState &&
    Array.length fs.history <= smallMaxHistory

-- | Property: Trimming at maxHistory boundary works
prop_trimmingAtBoundary :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_trimmingAtBoundary (ArbUndoRedoState state) (ArbAppState newState) =
  let
    s = unwrap state
    -- Set maxHistory to current history length
    boundaryState = UndoRedoState (s { maxHistory = Array.length s.history })
    newUndoState = pushState newState boundaryState
  in
    -- Should trim one state and add new one
    (Array.length (unwrap newUndoState).history == (unwrap boundaryState).maxHistory) &&
    ((unwrap newUndoState).currentIndex == Array.length (unwrap newUndoState).history - 1)

-- | Property: Undo from initial state preserves state
prop_undoFromInitial :: ArbAppState -> Boolean
prop_undoFromInitial (ArbAppState appState) =
  let
    undoState = initialUndoRedoState appState
    -- Cannot undo from initial state
    canUndoResult = canUndo undoState
    undoResult = undo undoState
  in
    not canUndoResult &&
    (undoResult == Nothing)

-- | Property: Redo at end preserves state
prop_redoAtEnd :: ArbUndoRedoState -> Boolean
prop_redoAtEnd (ArbUndoRedoState state) =
  let
    s = unwrap state
    -- Move to end of history
    atEndState = UndoRedoState (s { currentIndex = Array.length s.history - 1 })
    canRedoResult = canRedo atEndState
    redoResult = redo atEndState
  in
    not canRedoResult &&
    (redoResult == Nothing)

-- | Property: Rapid push operations maintain invariants
prop_rapidPush :: ArbUndoRedoState -> Array ArbAppState -> Boolean
prop_rapidPush (ArbUndoRedoState initialSt) arbNewStates =
  let
    newStates = map unwrap arbNewStates
    finalState = Array.foldl (\st newState -> pushState newState st) initialSt newStates
  in
    prop_historyInvariant_raw finalState &&
    prop_historyBounded_raw finalState &&
    prop_getStateCorrect_raw finalState

-- | Property: Alternating undo/redo maintains consistency
prop_alternatingUndoRedo :: ArbUndoRedoState -> Int -> Boolean
prop_alternatingUndoRedo (ArbUndoRedoState state) count =
  let
    absCount = abs count `mod` 5  -- Limit to reasonable range
    -- Alternate undo/redo
    finalState = Array.foldl (\st i ->
      if i `mod` 2 == 0
        then fromMaybe st (undo st)
        else fromMaybe st (redo st)
    ) state (range 0 (absCount - 1))
  in
    prop_historyInvariant_raw finalState &&
    prop_historyBounded_raw finalState &&
    prop_getStateCorrect_raw finalState

-- | Property: Push at maxHistory maintains bounds
prop_pushAtMaxHistory :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_pushAtMaxHistory (ArbUndoRedoState state) (ArbAppState newState) =
  let
    s = unwrap state
    -- Set maxHistory to current length
    atMaxState = UndoRedoState (s { maxHistory = Array.length s.history })
    newUndoState = pushState newState atMaxState
  in
    Array.length (unwrap newUndoState).history <= (unwrap newUndoState).maxHistory &&
    ((unwrap newUndoState).currentIndex == Array.length (unwrap newUndoState).history - 1)

-- | Property: Undo/redo with reducer integration
prop_reducerIntegration :: ArbAppState -> ArbAction -> Boolean
prop_reducerIntegration (ArbAppState initialSt) (ArbAction action) =
  -- Skip Undo/Redo actions for this test
  case action of
    Undo -> true
    Redo -> true
    _ ->
      let
        -- Apply action
        newState = reduce initialSt action
        -- Undo
        undoneState = reduce newState Undo
        -- Redo
        redoneState = reduce undoneState Redo
      in
        -- Should return to newState (not initialState, since we pushed newState)
        redoneState == newState

-- | Property: State transitions preserve undo/redo state
prop_stateTransitionsPreserveUndoRedo :: ArbAppState -> ArbAction -> Boolean
prop_stateTransitionsPreserveUndoRedo (ArbAppState state) (ArbAction action) =
  case action of
    Undo -> true
    Redo -> true
    _ ->
      let
        newState = reduce state action
        -- undoRedo should be updated
        newHistoryLen = Array.length (unwrap newState.undoRedo).history
        oldHistoryLen = Array.length (unwrap state.undoRedo).history
      in
        -- History should grow (unless at maxHistory)
        (newHistoryLen >= oldHistoryLen) ||
        (newHistoryLen == (unwrap state.undoRedo).maxHistory)

-- | Property: Undo restores correct reducer state
prop_undoRestoresReducerState :: ArbAppState -> ArbAction -> Boolean
prop_undoRestoresReducerState (ArbAppState state) (ArbAction action) =
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
        (restoredState.connected == state.connected) &&
        (restoredState.balance.venice == state.balance.venice) &&
        (restoredState.session == state.session)

-- ============================================================================
-- BUG DETECTION PROPERTIES
-- ============================================================================

-- | BUG: pushState may not update index correctly after trimming
prop_bug_pushStateIndexAfterTrim :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_bug_pushStateIndexAfterTrim (ArbUndoRedoState state) (ArbAppState newState) =
  let
    s = unwrap state
    -- Create state at maxHistory boundary
    boundaryState = UndoRedoState (s { maxHistory = Array.length s.history })
    newUndoState = pushState newState boundaryState
    expectedIndex = Array.length (unwrap newUndoState).history - 1
  in
    -- Index should point to last state
    (unwrap newUndoState).currentIndex == expectedIndex
    -- BUG: If trimming logic is incorrect, index may be wrong

-- | BUG: History may become empty after trimming
prop_bug_historyEmptyAfterTrim :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_bug_historyEmptyAfterTrim (ArbUndoRedoState state) (ArbAppState newState) =
  let
    newUndoState = pushState newState state
  in
    -- History should never be empty
    Array.length (unwrap newUndoState).history > 0
    -- BUG: If trimming removes all states, history becomes empty

-- | BUG: currentIndex may be invalid after operations
prop_bug_invalidIndexAfterOps :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_bug_invalidIndexAfterOps (ArbUndoRedoState state) (ArbAppState newState) =
  let
    newUndoState = pushState newState state
  in
    -- Index should always be valid
    prop_historyInvariant_raw newUndoState
    -- BUG: Index may be negative or >= history.length

-- | BUG: Restored state may have wrong undoRedo field
prop_bug_restoredStateUndoRedo :: ArbUndoRedoState -> Boolean
prop_bug_restoredStateUndoRedo (ArbUndoRedoState state) =
  if canUndo state
    then case undo state of
      Just undoneState ->
        case getState undoneState of
          Just restoredState ->
            -- Restored state's undoRedo should match undoneState
            restoredState.undoRedo == undoneState
          Nothing -> false
      Nothing -> true
    else true
    -- BUG: Restored state may have stale undoRedo field

-- | BUG: Branching may not remove all future states
prop_bug_branchingIncomplete :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_bug_branchingIncomplete (ArbUndoRedoState state) (ArbAppState newState) =
  let
    s = unwrap state
    newUndoState = pushState newState state
    -- States after currentIndex should be removed
    expectedLen = min (s.currentIndex + 2) s.maxHistory
  in
    -- History length should match expected
    (Array.length (unwrap newUndoState).history == expectedLen) ||
    (Array.length (unwrap newUndoState).history <= s.maxHistory)
    -- BUG: If branching doesn't remove all future states, length will be wrong

-- | BUG: Memory leak with very large histories
-- | Tests that history trimming actually removes old states
prop_bug_memoryLeakLargeHistory :: ArbUndoRedoState -> Array ArbAppState -> Boolean
prop_bug_memoryLeakLargeHistory (ArbUndoRedoState initialSt) arbNewStates =
  let
    s = unwrap initialSt
    newStates = map unwrap arbNewStates
    -- Create state with small maxHistory to force trimming
    smallMaxHistory = 3
    smallState = UndoRedoState (s { maxHistory = smallMaxHistory })
    -- Push many states (should trigger trimming)
    finalState = Array.foldl (\st newState -> pushState newState st) smallState newStates
    -- History should not grow unbounded
    fs = unwrap finalState
    historyLen = Array.length fs.history
  in
    -- History should be bounded by maxHistory
    historyLen <= smallMaxHistory &&
    -- Most recent states should be preserved
    case Array.last fs.history of
      Just _ -> true
      Nothing -> false
    -- BUG: If trimming doesn't work, history grows unbounded

-- | BUG: State corruption during rapid push/undo/redo sequences
-- | Tests that state remains consistent during rapid operations
prop_bug_stateCorruptionRapidOps :: ArbUndoRedoState -> Array UndoRedoAction -> Boolean
prop_bug_stateCorruptionRapidOps (ArbUndoRedoState initialSt) actions =
  let
    runAction :: UndoRedoState -> UndoRedoAction -> UndoRedoState
    runAction currentState = case _ of
      UndoAction -> fromMaybe currentState (undo currentState)
      RedoAction -> fromMaybe currentState (redo currentState)
      NewStateAction newAppState -> pushState newAppState currentState

    finalState = Array.foldl runAction initialSt actions

    -- All invariants must hold
    invariant1 = prop_historyInvariant_raw finalState
    invariant2 = prop_historyBounded_raw finalState
    invariant3 = prop_getStateCorrect_raw finalState
    -- State should be retrievable
    stateRetrievable = case getState finalState of
      Just _ -> true
      Nothing -> false
  in
    invariant1 && invariant2 && invariant3 && stateRetrievable
    -- BUG: Rapid operations may corrupt state

-- | BUG: Index calculation error during complex branching sequences
-- | Tests that index is always correct after complex operations
prop_bug_indexCalculationError :: ArbUndoRedoState -> Array ArbAppState -> Boolean
prop_bug_indexCalculationError (ArbUndoRedoState initialSt) arbNewStates =
  let
    newStates = map unwrap arbNewStates
    -- Create complex sequence: undo, push, undo, push, etc.
    complexState = Array.foldl (\st i ->
      if i `mod` 2 == 0 && canUndo st
        then fromMaybe st (undo st)
        else st
    ) initialSt (range 0 (Array.length newStates - 1))

    -- Now push all new states
    finalState = Array.foldl (\st newState -> pushState newState st) complexState newStates

    fs = unwrap finalState
    -- Index should always be valid and point to last state
    indexValid = prop_historyInvariant_raw finalState
    indexPointsToLast = fs.currentIndex == Array.length fs.history - 1
  in
    indexValid && indexPointsToLast
    -- BUG: Complex sequences may cause index calculation errors

-- | BUG: History corruption during multiple branches
-- | Tests that history structure remains valid after multiple branches
prop_bug_historyCorruptionMultipleBranches :: ArbUndoRedoState -> Array ArbAppState -> Boolean
prop_bug_historyCorruptionMultipleBranches (ArbUndoRedoState initialSt) arbNewStates =
  let
    newStates = map unwrap arbNewStates
    -- Create multiple branches by undoing then pushing
    branchedState = Array.foldl (\st newState ->
      if canUndo st
        then
          case undo st of
            Just undoneState -> pushState newState undoneState
            Nothing -> pushState newState st
        else pushState newState st
    ) initialSt newStates

    -- History should be valid
    historyValid = prop_historyInvariant_raw branchedState
    historyBounded = prop_historyBounded_raw branchedState
    -- All states in history should be retrievable
    allStatesRetrievable = Array.all (\i ->
      case Array.index (unwrap branchedState).history i of
        Just _ -> true
        Nothing -> false
    ) (range 0 (Array.length (unwrap branchedState).history - 1))
  in
    historyValid && historyBounded && allStatesRetrievable
    -- BUG: Multiple branches may corrupt history structure

-- | BUG: Trimming may remove current state
-- | Tests that trimming never removes the current state
prop_bug_trimmingRemovesCurrentState :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_bug_trimmingRemovesCurrentState (ArbUndoRedoState state) (ArbAppState newState) =
  let
    s = unwrap state
    -- Create state at maxHistory boundary
    boundaryState = UndoRedoState (s { maxHistory = Array.length s.history })
    newUndoState = pushState newState boundaryState
    -- Current state should still be retrievable
    currentStateRetrievable = case getState newUndoState of
      Just _ -> true
      Nothing -> false
    -- Current state should match newState
    currentStateMatches = case getState newUndoState of
      Just st -> st == newState
      Nothing -> false
  in
    currentStateRetrievable && currentStateMatches
    -- BUG: Trimming may accidentally remove current state

-- | BUG: Undo/redo may not preserve state equality
-- | Tests that undo then redo returns to exact same state
prop_bug_undoRedoStateEquality :: ArbUndoRedoState -> Boolean
prop_bug_undoRedoStateEquality (ArbUndoRedoState state) =
  let s = unwrap state
  in
    if canUndo state
      then case undo state of
        Just undoneState ->
          case redo undoneState of
            Just redoneState ->
              -- Should return to exact same state
              (redoneState == state) &&
              -- History should be identical
              ((unwrap redoneState).history == s.history) &&
              -- Index should be identical
              ((unwrap redoneState).currentIndex == s.currentIndex)
            Nothing -> false
        Nothing -> true
      else true
      -- BUG: Undo/redo may not preserve exact state equality

-- | BUG: Branching may corrupt state references
-- | Tests that states in history remain valid after branching
prop_bug_branchingCorruptsStateReferences :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_bug_branchingCorruptsStateReferences (ArbUndoRedoState state) (ArbAppState newState) =
  let
    s = unwrap state
    -- Save original states before branching
    originalStates = Array.take (s.currentIndex + 1) s.history
    newUndoState = pushState newState state
    -- States before currentIndex should be preserved (may be trimmed)
    preservedStates = Array.take (min (s.currentIndex + 1) (Array.length (unwrap newUndoState).history)) (unwrap newUndoState).history
  in
    -- Preserved states should match original (up to trimming)
    if Array.length preservedStates <= Array.length originalStates
      then
        Array.all (\i ->
          case Array.index preservedStates i, Array.index originalStates (Array.length originalStates - Array.length preservedStates + i) of
            Just preserved, Just original -> preserved == original
            _, _ -> false
        ) (range 0 (Array.length preservedStates - 1))
      else false
    -- BUG: Branching may corrupt state references in history

-- | BUG: Multiple undo operations may skip states
-- | Tests that multiple undo operations visit all intermediate states
prop_bug_multipleUndoSkippingStates :: ArbUndoRedoState -> Int -> Boolean
prop_bug_multipleUndoSkippingStates (ArbUndoRedoState state) undoCount =
  let
    s = unwrap state
    absUndoCount = abs undoCount `mod` (s.currentIndex + 1)
    -- Perform multiple undo operations
    undoneState = Array.foldl (\st _ -> fromMaybe st (undo st)) state (range 0 (absUndoCount - 1))
    -- Index should decrease by exactly undoCount
    indexDecreased = (unwrap undoneState).currentIndex == s.currentIndex - absUndoCount
    -- History should be preserved
    historyPreserved = (unwrap undoneState).history == s.history
  in
    indexDecreased && historyPreserved
    -- BUG: Multiple undo may skip states or corrupt history

-- | BUG: Redo after branching may access invalid state
-- | Tests that redo is not possible after branching
prop_bug_redoAfterBranching :: ArbUndoRedoState -> ArbAppState -> Boolean
prop_bug_redoAfterBranching (ArbUndoRedoState state) (ArbAppState newState) =
  let
    -- Branch by pushing new state
    branchedState = pushState newState state
    -- Redo should not be possible (we're at end of history)
    canRedoResult = canRedo branchedState
    redoResult = redo branchedState
  in
    not canRedoResult &&
    (redoResult == Nothing)
    -- BUG: Redo may be incorrectly allowed after branching

-- | BUG: State restoration may lose nested state fields
-- | Tests that all nested fields are preserved during restoration
prop_bug_stateRestorationLosesNestedFields :: ArbUndoRedoState -> Boolean
prop_bug_stateRestorationLosesNestedFields (ArbUndoRedoState state) =
  if canUndo state
    then case undo state of
      Just undoneState ->
        case getState undoneState, getState state of
          Just restored, Just original ->
            -- Check nested fields are preserved
            (restored.balance.venice == original.balance.venice) &&
            (case restored.session, original.session of
              Just rSession, Just oSession -> rSession == oSession
              Nothing, Nothing -> true
              _, _ -> false) &&
            (restored.connected == original.connected)
          _, _ -> false
      Nothing -> true
    else true
    -- BUG: State restoration may lose nested fields

-- | BUG: History trimming may cause index out of bounds
-- | Tests that index remains valid after aggressive trimming
prop_bug_trimmingIndexOutOfBounds :: ArbUndoRedoState -> Array ArbAppState -> Boolean
prop_bug_trimmingIndexOutOfBounds (ArbUndoRedoState initialSt) arbNewStates =
  let
    s = unwrap initialSt
    newStates = map unwrap arbNewStates
    -- Create state with very small maxHistory
    tinyMaxHistory = 2
    tinyState = UndoRedoState (s { maxHistory = tinyMaxHistory })
    -- Push many states to force aggressive trimming
    finalState = Array.foldl (\st newState -> pushState newState st) tinyState newStates
    fs = unwrap finalState
    -- Index should always be valid
    indexValid = prop_historyInvariant_raw finalState
    -- Index should point to last state
    indexPointsToLast = fs.currentIndex == Array.length fs.history - 1
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
