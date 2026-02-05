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
import Data.String.CodeUnits as String
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
import Sidepanel.State.Balance (VeniceBalance)
import Data.Maybe (Maybe(..))

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
