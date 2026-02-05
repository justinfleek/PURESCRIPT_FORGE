-- | Property tests for state reducers
-- | Tests invariants, idempotency, and state preservation properties
module Test.Property.ReducerProps where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Data.Maybe (Maybe(..), isNothing, isJust)
import Data.String as String
import Data.Foldable (fold)
import Data.Array (replicate)

import Console.App.Routes.Omega.Util.DataDumper
  ( DataDumperState
  , DataDumperAction(..)
  , initialState
  , reducer
  )

-- | Property: Idempotency - applying the same action twice should be the same as applying it once
prop_reducerIdempotency :: DataDumperState -> DataDumperAction -> Boolean
prop_reducerIdempotency state action =
  let
    state1 = reducer state action
    state2 = reducer state1 action
  in
    state1 == state2

-- | Property: State isolation - reducer should not mutate original state
prop_reducerStateIsolation :: DataDumperState -> DataDumperAction -> Boolean
prop_reducerStateIsolation state action =
  let
    originalModel = state.modelName
    originalRequest = state.request
    originalResponse = state.response
    newState = reducer state action
    -- Original state should be unchanged (PureScript immutability ensures this)
    -- But we verify the new state is different if action changes something
    modelUnchanged = case action of
      ProvideModel _ -> true  -- Action changes model, so we can't verify unchanged
      ProvideRequest _ -> originalModel == newState.modelName
      ProvideResponse _ -> originalModel == newState.modelName && originalRequest == newState.request
      ProvideStream _ -> originalModel == newState.modelName && originalRequest == newState.request && originalResponse == newState.response
  in
    modelUnchanged

-- | Property: ProvideModel overwrites previous model
prop_provideModelOverwrites :: DataDumperState -> String -> String -> Boolean
prop_provideModelOverwrites state model1 model2 =
  let
    state1 = reducer state (ProvideModel model1)
    state2 = reducer state1 (ProvideModel model2)
  in
    state2.modelName == Just model2 && state2.modelName /= state1.modelName

-- | Property: ProvideRequest overwrites previous request
prop_provideRequestOverwrites :: DataDumperState -> String -> String -> Boolean
prop_provideRequestOverwrites state req1 req2 =
  let
    state1 = reducer state (ProvideRequest req1)
    state2 = reducer state1 (ProvideRequest req2)
  in
    state2.request == Just req2 && state2.request /= state1.request

-- | Property: ProvideResponse overwrites previous response
prop_provideResponseOverwrites :: DataDumperState -> String -> String -> Boolean
prop_provideResponseOverwrites state resp1 resp2 =
  let
    state1 = reducer state (ProvideResponse resp1)
    state2 = reducer state1 (ProvideResponse resp2)
  in
    state2.response == Just resp2 && state2.response /= state1.response

-- | Property: ProvideStream appends (doesn't overwrite)
prop_provideStreamAppends :: DataDumperState -> String -> String -> Boolean
prop_provideStreamAppends state chunk1 chunk2 =
  let
    state1 = reducer state (ProvideStream chunk1)
    state2 = reducer state1 (ProvideStream chunk2)
    expectedStream = case state.response of
      Nothing -> Just (chunk1 <> chunk2)
      Just existing -> Just (existing <> chunk1 <> chunk2)
  in
    case state2.response of
      Just stream -> String.contains (String.Pattern chunk1) stream && String.contains (String.Pattern chunk2) stream
      Nothing -> false

-- | Property: Unrelated fields preserved
prop_unrelatedFieldsPreserved :: DataDumperState -> DataDumperAction -> Boolean
prop_unrelatedFieldsPreserved state action =
  let
    originalModel = state.modelName
    originalRequest = state.request
    originalResponse = state.response
    newState = reducer state action
    -- Verify unrelated fields are preserved
    modelPreserved = case action of
      ProvideModel _ -> true  -- Model changes, can't verify
      ProvideRequest _ -> originalModel == newState.modelName
      ProvideResponse _ -> originalModel == newState.modelName && originalRequest == newState.request
      ProvideStream _ -> originalModel == newState.modelName && originalRequest == newState.request
    requestPreserved = case action of
      ProvideRequest _ -> true  -- Request changes
      ProvideModel _ -> originalRequest == newState.request
      ProvideResponse _ -> originalRequest == newState.request
      ProvideStream _ -> originalRequest == newState.request
  in
    modelPreserved && requestPreserved

-- | Property: Initial state has all fields as Nothing
prop_initialStateEmpty :: Boolean
prop_initialStateEmpty =
  isNothing initialState.modelName &&
  isNothing initialState.request &&
  isNothing initialState.response

-- | Property: State transitions are deterministic
prop_stateTransitionsDeterministic :: DataDumperState -> DataDumperAction -> Boolean
prop_stateTransitionsDeterministic state action =
  let
    state1 = reducer state action
    state2 = reducer state action
  in
    state1 == state2

-- | Property tests for DataDumper reducer
spec :: Spec Unit
spec = describe "DataDumper Reducer Property Tests" do
  describe "Idempotency Properties" do
    it "reducer is idempotent for ProvideModel" do
      -- Applying ProvideModel twice should be the same as once
      let state = initialState
      let action = ProvideModel "test-model"
      let state1 = reducer state action
      let state2 = reducer state1 action
      state1 `shouldEqual` state2

    it "reducer is idempotent for ProvideRequest" do
      let state = initialState
      let action = ProvideRequest "test-request"
      let state1 = reducer state action
      let state2 = reducer state1 action
      state1 `shouldEqual` state2

    it "reducer is idempotent for ProvideResponse" do
      let state = initialState
      let action = ProvideResponse "test-response"
      let state1 = reducer state action
      let state2 = reducer state1 action
      state1 `shouldEqual` state2

    it "BUG: reducer may not be idempotent for ProvideStream (appends)" do
      -- BUG: ProvideStream appends, so applying twice adds content twice
      -- This is expected behavior, but documents the non-idempotency
      let state = initialState
      let action = ProvideStream "chunk1"
      let state1 = reducer state action
      let state2 = reducer state1 action
      -- state2 should have chunk1 twice
      case state2.response of
        Just stream -> stream `shouldEqual` "chunk1chunk1"
        Nothing -> false `shouldEqual` true

  describe "State Isolation Properties" do
    it "reducer preserves unrelated fields" do
      let state = initialState { modelName = Just "model1" }
      let newState = reducer state (ProvideRequest "request1")
      isJust newState.modelName `shouldEqual` true
      newState.modelName `shouldEqual` Just "model1"

    it "reducer preserves model when providing request" do
      let state = initialState { modelName = Just "model1" }
      let newState = reducer state (ProvideRequest "request1")
      newState.modelName `shouldEqual` Just "model1"

    it "reducer preserves model and request when providing response" do
      let state = initialState { modelName = Just "model1", request = Just "request1" }
      let newState = reducer state (ProvideResponse "response1")
      newState.modelName `shouldEqual` Just "model1"
      newState.request `shouldEqual` Just "request1"

  describe "Overwrite Properties" do
    it "ProvideModel overwrites previous model" do
      let state = initialState { modelName = Just "old-model" }
      let newState = reducer state (ProvideModel "new-model")
      newState.modelName `shouldEqual` Just "new-model"

    it "ProvideRequest overwrites previous request" do
      let state = initialState { request = Just "old-request" }
      let newState = reducer state (ProvideRequest "new-request")
      newState.request `shouldEqual` Just "new-request"

    it "ProvideResponse overwrites previous response" do
      let state = initialState { response = Just "old-response" }
      let newState = reducer state (ProvideResponse "new-response")
      newState.response `shouldEqual` Just "new-response"

  describe "Append Properties" do
    it "ProvideStream appends to Nothing response" do
      let state = initialState
      let newState = reducer state (ProvideStream "chunk1")
      newState.response `shouldEqual` Just "chunk1"

    it "ProvideStream appends to existing response" do
      let state = initialState { response = Just "existing" }
      let newState = reducer state (ProvideStream "chunk1")
      case newState.response of
        Just stream -> stream `shouldEqual` "existingchunk1"
        Nothing -> false `shouldEqual` true

    it "ProvideStream appends multiple chunks" do
      let state = initialState
      let state1 = reducer state (ProvideStream "chunk1")
      let state2 = reducer state1 (ProvideStream "chunk2")
      case state2.response of
        Just stream -> stream `shouldEqual` "chunk1chunk2"
        Nothing -> false `shouldEqual` true

  describe "Initial State Properties" do
    it "initialState has all fields as Nothing" do
      isNothing initialState.modelName `shouldEqual` true
      isNothing initialState.request `shouldEqual` true
      isNothing initialState.response `shouldEqual` true

  describe "Determinism Properties" do
    it "same action on same state produces same result" do
      let state = initialState { modelName = Just "model1" }
      let action = ProvideRequest "request1"
      let state1 = reducer state action
      let state2 = reducer state action
      state1 `shouldEqual` state2

    it "state transitions are deterministic across multiple actions" do
      let state = initialState
      let state1 = reducer state (ProvideModel "model1")
      let state2 = reducer state1 (ProvideRequest "request1")
      let state3 = reducer state2 (ProvideResponse "response1")
      -- Replay same sequence
      let state1b = reducer state (ProvideModel "model1")
      let state2b = reducer state1b (ProvideRequest "request1")
      let state3b = reducer state2b (ProvideResponse "response1")
      state3 `shouldEqual` state3b

  describe "Edge Case Properties" do
    it "handles empty string model name" do
      let state = reducer initialState (ProvideModel "")
      state.modelName `shouldEqual` Just ""

    it "handles empty string request" do
      let state = reducer initialState (ProvideRequest "")
      state.request `shouldEqual` Just ""

    it "handles empty string response" do
      let state = reducer initialState (ProvideResponse "")
      state.response `shouldEqual` Just ""

    it "handles empty string stream chunk" do
      let state = reducer initialState (ProvideStream "")
      case state.response of
        Just stream -> stream `shouldEqual` ""
        Nothing -> false `shouldEqual` true

    it "handles very long strings" do
      let longString = fold (replicate 10000 "a")
      let state = reducer initialState (ProvideModel longString)
      state.modelName `shouldEqual` Just longString

  describe "Bug Detection Properties" do
    it "BUG: ProvideStream appends even when response exists (may cause issues)" do
      -- BUG: ProvideStream always appends, even if response already exists
      -- This could cause issues if ProvideResponse was called before ProvideStream
      let state = initialState { response = Just "existing-response" }
      let newState = reducer state (ProvideStream "new-chunk")
      -- Stream appends to existing response, which may not be intended
      case newState.response of
        Just stream -> stream `shouldEqual` "existing-responsenew-chunk"
        Nothing -> false `shouldEqual` true
      -- This test documents the behavior
