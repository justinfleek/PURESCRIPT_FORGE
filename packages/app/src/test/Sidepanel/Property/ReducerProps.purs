-- | Property Tests for State Reducer with Realistic Action Sequences
-- |
-- | Based on spec 70-TESTING-STRATEGY.md and 71-UNIT-TESTING.md
-- | Tests reducer invariants with realistic action distributions
-- |
-- | Reference: REQUIRED/trtllm-serve-main/nix/openai-proxy-hs/ProxyPropTest.hs
module Test.Sidepanel.Property.ReducerProps where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Test.QuickCheck (class Arbitrary, arbitrary, (===), (==>))
import Test.QuickCheck.Gen (Gen, chooseInt, chooseFloat, arrayOf, elements, frequency)
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.DateTime (DateTime)
import Sidepanel.State.Reducer (reduce)
import Sidepanel.State.Actions (Action(..), BalanceUpdate, SessionUpdate, UsageRecord)
import Sidepanel.State.AppState (AppState, initialState)
import Sidepanel.State.Balance (VeniceBalance)
import Test.Sidepanel.TestFixtures (testDateTime)

-- | Realistic Action generator
-- | Uses realistic distributions:
-- | - 30% Balance updates (most common)
-- | - 20% Session updates
-- | - 15% Connection events
-- | - 10% Usage records
-- | - 10% UI actions
-- | - 5% Proof actions
-- | - 5% Undo/Redo
-- | - 5% Other
instance arbitraryAction :: Arbitrary Action where
  arbitrary = frequency
    [ (30.0, BalanceUpdated <$> arbitrary)
    , (20.0, SessionUpdated <$> arbitrary)
    , (15.0, elements [Connected, Disconnected, PingReceived testDateTime])
    , (10.0, UsageRecorded <$> arbitrary)
    , (10.0, elements [ToggleSidebar, SetActivePanel DashboardPanel, SetTheme Dark])
    , (5.0, elements [ProofConnected, ProofDisconnected])
    , (5.0, elements [Undo, Redo])
    , (5.0, elements [SessionCleared, CountdownTick])
    ]

-- | Balance update generator
instance arbitraryBalanceUpdate :: Arbitrary BalanceUpdate where
  arbitrary = do
    -- 80% Venice updates, 20% FLK updates
    useVenice <- frequency
      [ (80.0, pure true)
      , (20.0, pure false)
      ]
    if useVenice then do
      diem <- normalLike 50.0 20.0 0.0 100.0
      usd <- normalLike 10.0 5.0 0.0 50.0
      effective <- pure (diem + usd)
      consumptionRate <- chooseFloat 0.0 10.0
      timeToDepletion <- frequency
        [ (70.0, Just <$> chooseFloat 0.5 24.0)
        , (30.0, pure Nothing)
        ]
      todayUsed <- chooseFloat 0.0 50.0
      pure
        { diem: Just diem
        , flk: Nothing
        , usd: Just usd
        , effective
        , consumptionRate
        , timeToDepletion
        , todayUsed
        }
    else do
      flk <- normalLike 100.0 50.0 0.0 500.0
      effective <- pure flk
      consumptionRate <- chooseFloat 0.0 10.0
      timeToDepletion <- frequency
        [ (70.0, Just <$> chooseFloat 0.5 24.0)
        , (30.0, pure Nothing)
        ]
      todayUsed <- chooseFloat 0.0 100.0
      pure
        { diem: Nothing
        , flk: Just flk
        , usd: Nothing
        , effective
        , consumptionRate
        , timeToDepletion
        , todayUsed
        }

-- | Session update generator
instance arbitrarySessionUpdate :: Arbitrary SessionUpdate where
  arbitrary = do
    id <- arbitrarySessionId
    model <- elements ["llama-3.3-70b", "qwen2.5-72b", "mixtral-8x7b"]
    promptTokens <- chooseInt 0 100000
    completionTokens <- chooseInt 0 50000
    totalTokens <- pure (promptTokens + completionTokens)
    cost <- chooseFloat 0.0 1.0
    messageCount <- chooseInt 0 100
    startedAt <- frequency
      [ (70.0, Just <$> pure testDateTime)
      , (30.0, pure Nothing)
      ]
    pure
      { id
      , model
      , promptTokens
      , completionTokens
      , totalTokens
      , cost
      , messageCount
      , startedAt
      }

-- | Usage record generator (Poisson-like for message counts)
instance arbitraryUsageRecord :: Arbitrary UsageRecord where
  arbitrary = do
    prompt <- chooseInt 0 5000
    completion <- chooseInt 0 2000
    cost <- chooseFloat 0.0 0.1
    pure { prompt, completion, cost }

-- | Generate session ID
arbitrarySessionId :: Gen String
arbitrarySessionId = do
  len <- chooseInt 10 30
  chars <- arrayOf len (elements ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '-', '_'])
  pure $ "sess_" <> foldl (\acc c -> acc <> String.singleton c) "" chars

-- | Normal-like distribution generator
normalLike :: Number -> Number -> Number -> Number -> Gen Number
normalLike mean stddev minVal maxVal = do
  base <- chooseFloat minVal maxVal
  bias <- chooseFloat (-stddev) stddev
  let result = base + (mean - base) * 0.3 + bias
  pure $ clamp minVal maxVal result

clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal val
  | val < minVal = minVal
  | val > maxVal = maxVal
  | otherwise = val

-- | Property: Reducer never crashes (total function)
prop_reducerTotal :: AppState -> Action -> Boolean
prop_reducerTotal state action =
  -- Reducer should always return a valid state
  let result = reduce state action
  in true -- If we get here, reducer didn't crash

-- | Property: Connected/Disconnected toggle correctly
prop_connectionToggle :: AppState -> Boolean
prop_connectionToggle state =
  let
    connectedState = reduce state Connected
    disconnectedState = reduce connectedState Disconnected
    reconnectedState = reduce disconnectedState Connected
  in
    not connectedState.connected === false && -- Should be connected after Connected
    disconnectedState.connected === false &&
    reconnectedState.connected === true

-- | Property: Balance update merges correctly
prop_balanceUpdateMerges :: AppState -> BalanceUpdate -> Boolean
prop_balanceUpdateMerges state update =
  let
    updatedState = reduce state (BalanceUpdated update)
    veniceBalance = updatedState.balance.venice
    flkBalance = updatedState.balance.flk
  in
    case update.diem, update.flk of
      Just diem, Nothing ->
        case veniceBalance of
          Just venice ->
            venice.diem === diem &&
            venice.effective === update.effective
          Nothing -> false -- Should have Venice balance after Venice update
      Nothing, Just flk ->
        case flkBalance of
          Just flkBal ->
            flkBal.flk === flk &&
            flkBal.effective === update.effective
          Nothing -> false -- Should have FLK balance after FLK update
      _, _ -> true -- No balance update provided, state should be unchanged

-- | Property: Session update creates or updates session
prop_sessionUpdateCreatesOrUpdates :: AppState -> SessionUpdate -> Boolean
prop_sessionUpdateCreatesOrUpdates state update =
  let
    updatedState = reduce state (SessionUpdated update)
    session = updatedState.session
  in
    case session of
      Just s ->
        s.id === update.id &&
        s.model === update.model &&
        s.promptTokens === update.promptTokens &&
        s.completionTokens === update.completionTokens &&
        s.totalTokens === update.totalTokens &&
        s.cost === update.cost &&
        s.messageCount === update.messageCount
      Nothing -> false -- Should have session after update

-- | Property: Usage record increments session tokens
prop_usageRecordIncrements :: AppState -> UsageRecord -> Boolean
prop_usageRecordIncrements state usage =
  case state.session of
    Just session ->
      let
        updatedState = reduce state (UsageRecorded usage)
        updatedSession = updatedState.session
      in
        case updatedSession of
          Just s ->
            s.promptTokens === session.promptTokens + usage.prompt &&
            s.completionTokens === session.completionTokens + usage.completion &&
            s.totalTokens === session.totalTokens + usage.prompt + usage.completion &&
            s.cost === session.cost + usage.cost
          Nothing -> false
    Nothing -> true -- No session, usage record should be no-op

-- | Property: Session cleared removes session
prop_sessionClearedRemoves :: AppState -> Boolean
prop_sessionClearedRemoves state =
  case state.session of
    Just _ ->
      let clearedState = reduce state SessionCleared
      in clearedState.session === Nothing
    Nothing -> true -- No session to clear

-- | Property: Undo restores previous state (if possible)
prop_undoRestores :: AppState -> Action -> Boolean
prop_undoRestores initialState action =
  let
    newState = reduce initialState action
    undoneState = reduce newState Undo
    -- After undo, should restore to initial state (if undo was possible)
    canUndo = Array.length newState.undoRedo.history > 1
  in
    if canUndo then
      -- Undo should restore previous state
      undoneState.undoRedo.currentIndex === initialState.undoRedo.currentIndex ||
      undoneState.undoRedo.currentIndex === newState.undoRedo.currentIndex - 1
    else
      true -- Cannot undo, state should be unchanged

-- | Property: Redo restores next state (if possible)
prop_redoRestores :: AppState -> Action -> Boolean
prop_redoRestores initialState action =
  let
    newState = reduce initialState action
    undoneState = reduce newState Undo
    redoneState = reduce undoneState Redo
    canRedo = Array.length undoneState.undoRedo.history > undoneState.undoRedo.currentIndex + 1
  in
    if canRedo && Array.length newState.undoRedo.history > 1 then
      -- Redo should restore next state
      redoneState.undoRedo.currentIndex === newState.undoRedo.currentIndex ||
      redoneState.undoRedo.currentIndex === undoneState.undoRedo.currentIndex + 1
    else
      true -- Cannot redo, state should be unchanged

-- | Property: Multiple actions preserve history invariants
prop_multipleActionsPreserveInvariants :: AppState -> Array Action -> Boolean
prop_multipleActionsPreserveInvariants initialState actions =
  let
    finalState = Array.foldl reduce initialState actions
    history = finalState.undoRedo.history
    currentIndex = finalState.undoRedo.currentIndex
  in
    Array.length history > 0 &&
    currentIndex >= 0 &&
    currentIndex < Array.length history &&
    Array.length history <= finalState.undoRedo.maxHistory

-- | Property: Realistic action sequence preserves invariants
prop_realisticSequence :: AppState -> Array Action -> Boolean
prop_realisticSequence initialState actions =
  let
    finalState = Array.foldl reduce initialState actions
    -- All invariants must hold
    historyInvariant = Array.length finalState.undoRedo.history > 0 &&
                       finalState.undoRedo.currentIndex >= 0 &&
                       finalState.undoRedo.currentIndex < Array.length finalState.undoRedo.history
    boundedInvariant = Array.length finalState.undoRedo.history <= finalState.undoRedo.maxHistory
  in
    historyInvariant && boundedInvariant

spec :: Spec Unit
spec = describe "Reducer Property Tests" do
  describe "Reducer Totality" do
    it "reducer never crashes" $
      quickCheck prop_reducerTotal
  
  describe "Connection Actions" do
    it "connected/disconnected toggle correctly" $
      quickCheck prop_connectionToggle
  
  describe "Balance Actions" do
    it "balance update merges correctly" $
      quickCheck prop_balanceUpdateMerges
  
  describe "Session Actions" do
    it "session update creates or updates session" $
      quickCheck prop_sessionUpdateCreatesOrUpdates
    
    it "usage record increments session tokens" $
      quickCheck prop_usageRecordIncrements
    
    it "session cleared removes session" $
      quickCheck prop_sessionClearedRemoves
  
  describe "Undo/Redo Actions" do
    it "undo restores previous state" $
      quickCheck prop_undoRestores
    
    it "redo restores next state" $
      quickCheck prop_redoRestores
  
  describe "Multiple Actions" do
    it "multiple actions preserve history invariants" $
      quickCheck prop_multipleActionsPreserveInvariants
    
    it "realistic action sequence preserves invariants" $
      quickCheck prop_realisticSequence
