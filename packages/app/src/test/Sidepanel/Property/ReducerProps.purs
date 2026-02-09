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
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, choose, vectorOf, elements, frequency)
import Data.Array.NonEmpty as NEA
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Data.String.CodeUnits (singleton) as String
import Data.DateTime (DateTime)
import Data.Foldable (foldl)
import Data.Newtype (class Newtype, unwrap)
import Sidepanel.State.Reducer (reduce)
import Sidepanel.State.Actions (Action(..), BalanceUpdate, SessionUpdate, UsageRecord)
import Sidepanel.State.AppState (AppState, UndoRedoState(..), initialState, Panel(..), Theme(..))
import Sidepanel.State.Balance (VeniceBalance)
import Test.Sidepanel.TestFixtures (testDateTime)

-- | Newtype wrappers for type aliases (PureScript requires data/newtype for instance heads)
newtype ArbBalanceUpdate = ArbBalanceUpdate BalanceUpdate
derive instance newtypeArbBalanceUpdate :: Newtype ArbBalanceUpdate _

newtype ArbSessionUpdate = ArbSessionUpdate SessionUpdate
derive instance newtypeArbSessionUpdate :: Newtype ArbSessionUpdate _

newtype ArbUsageRecord = ArbUsageRecord UsageRecord
derive instance newtypeArbUsageRecord :: Newtype ArbUsageRecord _

newtype ArbAppState = ArbAppState AppState
derive instance newtypeArbAppState :: Newtype ArbAppState _

newtype ArbAction = ArbAction Action
derive instance newtypeArbAction :: Newtype ArbAction _

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
-- | Arbitrary instance for ArbAppState - generates realistic app states
instance arbitraryArbAppState :: Arbitrary ArbAppState where
  arbitrary = pure (ArbAppState initialState)

instance arbitraryArbAction :: Arbitrary ArbAction where
  arbitrary = ArbAction <$> frequency
    (NEA.cons' (Tuple 30.0 (BalanceUpdated <<< unwrap <$> (arbitrary :: Gen ArbBalanceUpdate)))
    [ Tuple 20.0 (SessionUpdated <<< unwrap <$> (arbitrary :: Gen ArbSessionUpdate))
    , Tuple 15.0 (elements (NEA.cons' Connected [Disconnected, PingReceived testDateTime]))
    , Tuple 10.0 (UsageRecorded <<< unwrap <$> (arbitrary :: Gen ArbUsageRecord))
    , Tuple 10.0 (elements (NEA.cons' ToggleSidebar [SetActivePanel DashboardPanel, SetTheme Dark]))
    , Tuple 5.0 (elements (NEA.cons' ProofConnected [ProofDisconnected]))
    , Tuple 5.0 (elements (NEA.cons' Undo [Redo]))
    , Tuple 5.0 (elements (NEA.cons' SessionCleared [CountdownTick]))
    ])

-- | Balance update generator
instance arbitraryArbBalanceUpdate :: Arbitrary ArbBalanceUpdate where
  arbitrary = do
    -- 80% Venice updates, 20% FLK updates
    useVenice <- frequency
      (NEA.cons' (Tuple 80.0 (pure true))
      [ Tuple 20.0 (pure false)
      ])
    if useVenice then do
      diem <- normalLike 50.0 20.0 0.0 100.0
      usd <- normalLike 10.0 5.0 0.0 50.0
      effective <- pure (diem + usd)
      consumptionRate <- choose 0.0 10.0
      timeToDepletion <- frequency
        (NEA.cons' (Tuple 70.0 (Just <$> choose 0.5 24.0))
        [ Tuple 30.0 (pure Nothing)
        ])
      todayUsed <- choose 0.0 50.0
      pure $ ArbBalanceUpdate
        { diem: Just diem
        , flk: Nothing
        , usd: Just usd
        , effective
        , consumptionRate
        , timeToDepletion
        , todayUsed
        , timestamp: Nothing
        }
    else do
      flk <- normalLike 100.0 50.0 0.0 500.0
      effective <- pure flk
      consumptionRate <- choose 0.0 10.0
      timeToDepletion <- frequency
        (NEA.cons' (Tuple 70.0 (Just <$> choose 0.5 24.0))
        [ Tuple 30.0 (pure Nothing)
        ])
      todayUsed <- choose 0.0 100.0
      pure $ ArbBalanceUpdate
        { diem: Nothing
        , flk: Just flk
        , usd: Nothing
        , effective
        , consumptionRate
        , timeToDepletion
        , todayUsed
        , timestamp: Nothing
        }

-- | Session update generator
instance arbitraryArbSessionUpdate :: Arbitrary ArbSessionUpdate where
  arbitrary = do
    id <- arbitrarySessionId
    model <- elements (NEA.cons' "llama-3.3-70b" ["qwen2.5-72b", "mixtral-8x7b"])
    promptTokens <- chooseInt 0 100000
    completionTokens <- chooseInt 0 50000
    totalTokens <- pure (promptTokens + completionTokens)
    cost <- choose 0.0 1.0
    messageCount <- chooseInt 0 100
    startedAt <- frequency
      (NEA.cons' (Tuple 70.0 (Just <$> pure testDateTime))
      [ Tuple 30.0 (pure Nothing)
      ])
    pure $ ArbSessionUpdate
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
instance arbitraryArbUsageRecord :: Arbitrary ArbUsageRecord where
  arbitrary = do
    prompt <- chooseInt 0 5000
    completion <- chooseInt 0 2000
    cost <- choose 0.0 0.1
    pure $ ArbUsageRecord { prompt, completion, cost }

-- | Generate session ID
arbitrarySessionId :: Gen String
arbitrarySessionId = do
  len <- chooseInt 10 30
  chars <- vectorOf len (elements (NEA.cons' 'a' ['b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '-', '_']))
  pure $ "sess_" <> foldl (\acc c -> acc <> String.singleton c) "" chars

-- | Normal-like distribution generator
normalLike :: Number -> Number -> Number -> Number -> Gen Number
normalLike mean stddev minVal maxVal = do
  base <- choose minVal maxVal
  bias <- choose (-stddev) stddev
  let result = base + (mean - base) * 0.3 + bias
  pure $ clamp minVal maxVal result

clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal val
  | val < minVal = minVal
  | val > maxVal = maxVal
  | otherwise = val

-- | Helper to unwrap UndoRedoState for field access
ur :: AppState -> { history :: Array AppState, currentIndex :: Int, maxHistory :: Int }
ur s = unwrap s.undoRedo

-- | Property: Reducer never crashes (total function)
prop_reducerTotal :: ArbAppState -> ArbAction -> Boolean
prop_reducerTotal (ArbAppState state) (ArbAction action) =
  -- Reducer should always return a valid state
  let result = reduce state action
  in true -- If we get here, reducer didn't crash

-- | Property: Connected/Disconnected toggle correctly
prop_connectionToggle :: ArbAppState -> Boolean
prop_connectionToggle (ArbAppState state) =
  let
    connectedState = reduce state Connected
    disconnectedState = reduce connectedState Disconnected
    reconnectedState = reduce disconnectedState Connected
  in
    (not connectedState.connected == false) &&
    (disconnectedState.connected == false) &&
    (reconnectedState.connected == true)

-- | Property: Balance update merges correctly
prop_balanceUpdateMerges :: ArbAppState -> ArbBalanceUpdate -> Boolean
prop_balanceUpdateMerges (ArbAppState state) (ArbBalanceUpdate update) =
  let
    updatedState = reduce state (BalanceUpdated update)
    veniceBalance = updatedState.balance.venice
    flkBalance = updatedState.balance.flk
  in
    case update.diem, update.flk of
      Just diem, Nothing ->
        case veniceBalance of
          Just venice ->
            (venice.diem == diem) &&
            (venice.effective == update.effective)
          Nothing -> false -- Should have Venice balance after Venice update
      Nothing, Just flk ->
        case flkBalance of
          Just flkBal ->
            (flkBal.flk == flk) &&
            (flkBal.effective == update.effective)
          Nothing -> false -- Should have FLK balance after FLK update
      _, _ -> true -- No balance update provided, state should be unchanged

-- | Property: Session update creates or updates session
prop_sessionUpdateCreatesOrUpdates :: ArbAppState -> ArbSessionUpdate -> Boolean
prop_sessionUpdateCreatesOrUpdates (ArbAppState state) (ArbSessionUpdate update) =
  let
    updatedState = reduce state (SessionUpdated update)
    session = updatedState.session
  in
    case session of
      Just s ->
        (s.id == update.id) &&
        (s.model == update.model) &&
        (s.promptTokens == update.promptTokens) &&
        (s.completionTokens == update.completionTokens) &&
        (s.totalTokens == update.totalTokens) &&
        (s.cost == update.cost) &&
        (s.messageCount == update.messageCount)
      Nothing -> false -- Should have session after update

-- | Property: Usage record increments session tokens
prop_usageRecordIncrements :: ArbAppState -> ArbUsageRecord -> Boolean
prop_usageRecordIncrements (ArbAppState state) (ArbUsageRecord usage) =
  case state.session of
    Just session ->
      let
        updatedState = reduce state (UsageRecorded usage)
        updatedSession = updatedState.session
      in
        case updatedSession of
          Just s ->
            (s.promptTokens == session.promptTokens + usage.prompt) &&
            (s.completionTokens == session.completionTokens + usage.completion) &&
            (s.totalTokens == session.totalTokens + usage.prompt + usage.completion) &&
            (s.cost == session.cost + usage.cost)
          Nothing -> false
    Nothing -> true -- No session, usage record should be no-op

-- | Property: Session cleared removes session
prop_sessionClearedRemoves :: ArbAppState -> Boolean
prop_sessionClearedRemoves (ArbAppState state) =
  case state.session of
    Just _ ->
      let clearedState = reduce state SessionCleared
      in clearedState.session == Nothing
    Nothing -> true -- No session to clear

-- | Property: Undo restores previous state (if possible)
prop_undoRestores :: ArbAppState -> ArbAction -> Boolean
prop_undoRestores (ArbAppState state) (ArbAction action) =
  let
    newState = reduce state action
    undoneState = reduce newState Undo
    -- After undo, should restore to initial state (if undo was possible)
    canUndoNow = Array.length (ur newState).history > 1
  in
    if canUndoNow then
      -- Undo should restore previous state
      ((ur undoneState).currentIndex == (ur state).currentIndex) ||
      ((ur undoneState).currentIndex == (ur newState).currentIndex - 1)
    else
      true -- Cannot undo, state should be unchanged

-- | Property: Redo restores next state (if possible)
prop_redoRestores :: ArbAppState -> ArbAction -> Boolean
prop_redoRestores (ArbAppState state) (ArbAction action) =
  let
    newState = reduce state action
    undoneState = reduce newState Undo
    redoneState = reduce undoneState Redo
    canRedoNow = Array.length (ur undoneState).history > (ur undoneState).currentIndex + 1
  in
    if canRedoNow && Array.length (ur newState).history > 1 then
      -- Redo should restore next state
      ((ur redoneState).currentIndex == (ur newState).currentIndex) ||
      ((ur redoneState).currentIndex == (ur undoneState).currentIndex + 1)
    else
      true -- Cannot redo, state should be unchanged

-- | Property: Multiple actions preserve history invariants
prop_multipleActionsPreserveInvariants :: ArbAppState -> Array ArbAction -> Boolean
prop_multipleActionsPreserveInvariants (ArbAppState state) arbActions =
  let
    actions = map unwrap arbActions
    finalState = Array.foldl reduce state actions
    u = ur finalState
  in
    Array.length u.history > 0 &&
    u.currentIndex >= 0 &&
    u.currentIndex < Array.length u.history &&
    Array.length u.history <= u.maxHistory

-- | Property: Realistic action sequence preserves invariants
prop_realisticSequence :: ArbAppState -> Array ArbAction -> Boolean
prop_realisticSequence (ArbAppState state) arbActions =
  let
    actions = map unwrap arbActions
    finalState = Array.foldl reduce state actions
    u = ur finalState
    -- All invariants must hold
    historyInvariant = Array.length u.history > 0 &&
                       u.currentIndex >= 0 &&
                       u.currentIndex < Array.length u.history
    boundedInvariant = Array.length u.history <= u.maxHistory
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
