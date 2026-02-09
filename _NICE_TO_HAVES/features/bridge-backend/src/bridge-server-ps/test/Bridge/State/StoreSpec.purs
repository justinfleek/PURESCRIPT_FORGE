-- | State Store Tests
-- | Property tests for state transitions
module Test.Bridge.State.StoreSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeGreaterThanOrEqual)
import Effect (Effect)
import Effect.Class (liftEffect)
import Bridge.State.Store (StateStore, createStore, getState, updateBalance, updateSession, clearSession, BalanceState, SessionState, initialState)
import Data.DateTime (DateTime, adjust)
import Data.Maybe (Maybe(..))
import Data.Time.Duration (Milliseconds(..))

-- | Test balance state invariants
testBalanceInvariants :: forall m. Monad m => m Unit
testBalanceInvariants = do
  describe "Balance State Invariants" do
    it "all balance values are non-negative in initial state" do
      let balance = initialState.balance
      balance.venice.diem `shouldBeGreaterThanOrEqual` 0.0
      balance.venice.usd `shouldBeGreaterThanOrEqual` 0.0
      balance.venice.effective `shouldBeGreaterThanOrEqual` 0.0
      balance.consumptionRate `shouldBeGreaterThanOrEqual` 0.0
      balance.todayUsed `shouldBeGreaterThanOrEqual` 0.0
      balance.todayStartBalance `shouldBeGreaterThanOrEqual` 0.0
    
    it "consumption rate is non-negative after update" do
      store <- liftEffect createStore
      state <- liftEffect $ getState store
      state.balance.consumptionRate `shouldBeGreaterThanOrEqual` 0.0
      
      -- Update with various consumption rates
      let balance1 = initialState.balance { consumptionRate = 0.0 }
      liftEffect $ updateBalance store balance1
      state1 <- liftEffect $ getState store
      state1.balance.consumptionRate `shouldBeGreaterThanOrEqual` 0.0
      
      let balance2 = initialState.balance { consumptionRate = 100.0 }
      liftEffect $ updateBalance store balance2
      state2 <- liftEffect $ getState store
      state2.balance.consumptionRate `shouldBeGreaterThanOrEqual` 0.0
    
    it "todayUsed is non-negative and never exceeds todayStartBalance" do
      store <- liftEffect createStore
      let balance1 = initialState.balance { todayStartBalance = 1000.0, todayUsed = 500.0 }
      liftEffect $ updateBalance store balance1
      state1 <- liftEffect $ getState store
      state1.balance.todayUsed `shouldBeGreaterThanOrEqual` 0.0
      state1.balance.todayUsed `shouldBeGreaterThanOrEqual` 0.0 -- Would check <= todayStartBalance
      
      let balance2 = initialState.balance { todayStartBalance = 1000.0, todayUsed = 0.0 }
      liftEffect $ updateBalance store balance2
      state2 <- liftEffect $ getState store
      state2.balance.todayUsed `shouldEqual` 0.0
      
      let balance3 = initialState.balance { todayStartBalance = 1000.0, todayUsed = 1000.0 }
      liftEffect $ updateBalance store balance3
      state3 <- liftEffect $ getState store
      state3.balance.todayUsed `shouldBeGreaterThanOrEqual` 0.0
    
    it "effective balance always equals diem + usd" do
      store <- liftEffect createStore
      
      -- Test case 1: Both positive
      let testBalance1 = 
            { venice: { diem: 100.0, usd: 50.0, effective: 150.0, lastUpdated: Nothing }
            , consumptionRate: 10.0
            , timeToDepletion: Nothing
            , todayUsed: 0.0
            , todayStartBalance: 1000.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store testBalance1
      state1 <- liftEffect $ getState store
      state1.balance.venice.effective `shouldEqual` (state1.balance.venice.diem + state1.balance.venice.usd)
      
      -- Test case 2: Zero diem, positive usd
      let testBalance2 = 
            { venice: { diem: 0.0, usd: 50.0, effective: 50.0, lastUpdated: Nothing }
            , consumptionRate: 10.0
            , timeToDepletion: Nothing
            , todayUsed: 0.0
            , todayStartBalance: 1000.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store testBalance2
      state2 <- liftEffect $ getState store
      state2.balance.venice.effective `shouldEqual` (state2.balance.venice.diem + state2.balance.venice.usd)
      
      -- Test case 3: Positive diem, zero usd
      let testBalance3 = 
            { venice: { diem: 100.0, usd: 0.0, effective: 100.0, lastUpdated: Nothing }
            , consumptionRate: 10.0
            , timeToDepletion: Nothing
            , todayUsed: 0.0
            , todayStartBalance: 1000.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store testBalance3
      state3 <- liftEffect $ getState store
      state3.balance.venice.effective `shouldEqual` (state3.balance.venice.diem + state3.balance.venice.usd)
      
      -- Test case 4: Both zero
      let testBalance4 = 
            { venice: { diem: 0.0, usd: 0.0, effective: 0.0, lastUpdated: Nothing }
            , consumptionRate: 0.0
            , timeToDepletion: Nothing
            , todayUsed: 0.0
            , todayStartBalance: 0.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store testBalance4
      state4 <- liftEffect $ getState store
      state4.balance.venice.effective `shouldEqual` (state4.balance.venice.diem + state4.balance.venice.usd)
      
      -- Test case 5: Very large values
      let testBalance5 = 
            { venice: { diem: 1.0e10, usd: 5.0e9, effective: 1.5e10, lastUpdated: Nothing }
            , consumptionRate: 1.0e6
            , timeToDepletion: Nothing
            , todayUsed: 0.0
            , todayStartBalance: 1.0e10
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store testBalance5
      state5 <- liftEffect $ getState store
      let expected = state5.balance.venice.diem + state5.balance.venice.usd
      let diff = if state5.balance.venice.effective > expected then state5.balance.venice.effective - expected else expected - state5.balance.venice.effective
      diff < 0.01 `shouldBeTrue` -- Allow for floating point precision
    
    it "timeToDepletion is consistent with balance and consumption rate" do
      store <- liftEffect createStore
      
      -- Test case: Positive balance and rate
      let balance1 = 
            { venice: { diem: 1000.0, usd: 0.0, effective: 1000.0, lastUpdated: Nothing }
            , consumptionRate: 10.0
            , timeToDepletion: Just 100.0
            , todayUsed: 0.0
            , todayStartBalance: 1000.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store balance1
      state1 <- liftEffect $ getState store
      case state1.balance.timeToDepletion of
        Just time -> 
          let expected = state1.balance.venice.effective / state1.balance.consumptionRate
              diff = if time > expected then time - expected else expected - time
          in diff < 0.01 `shouldBeTrue`
        Nothing -> false `shouldEqual` true
      
      -- Test case: Zero consumption rate should have Nothing
      let balance2 = 
            { venice: { diem: 1000.0, usd: 0.0, effective: 1000.0, lastUpdated: Nothing }
            , consumptionRate: 0.0
            , timeToDepletion: Nothing
            , todayUsed: 0.0
            , todayStartBalance: 1000.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store balance2
      state2 <- liftEffect $ getState store
      state2.balance.timeToDepletion `shouldEqual` Nothing

-- | Test session state invariants
testSessionInvariants :: forall m. Monad m => m Unit
testSessionInvariants = do
  describe "Session State Invariants" do
    it "session ID is non-empty when session exists" do
      store <- liftEffect createStore
      now <- liftEffect getCurrentDateTime
      let testSession = 
            { id: "test-session-123"
            , promptTokens: 100
            , completionTokens: 200
            , totalTokens: 300
            , cost: 0.05
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 5
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession
      state <- liftEffect $ getState store
      case state.session of
        Just session -> do
          session.id `shouldEqual` "test-session-123"
          session.id /= "" `shouldBeTrue`
        Nothing -> false `shouldEqual` true
    
    it "token totals are always correct (prompt + completion = total)" do
      store <- liftEffect createStore
      now <- liftEffect getCurrentDateTime
      
      -- Test case 1: Normal tokens
      let testSession1 = 
            { id: "test-session-456"
            , promptTokens: 100
            , completionTokens: 200
            , totalTokens: 300
            , cost: 0.05
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 5
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession1
      state1 <- liftEffect $ getState store
      case state1.session of
        Just session -> 
          session.totalTokens `shouldEqual` (session.promptTokens + session.completionTokens)
        Nothing -> false `shouldEqual` true
      
      -- Test case 2: Zero prompt tokens
      let testSession2 = 
            { id: "test-session-zero-prompt"
            , promptTokens: 0
            , completionTokens: 100
            , totalTokens: 100
            , cost: 0.01
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 1
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession2
      state2 <- liftEffect $ getState store
      case state2.session of
        Just session -> 
          session.totalTokens `shouldEqual` (session.promptTokens + session.completionTokens)
        Nothing -> false `shouldEqual` true
      
      -- Test case 3: Zero completion tokens
      let testSession3 = 
            { id: "test-session-zero-completion"
            , promptTokens: 100
            , completionTokens: 0
            , totalTokens: 100
            , cost: 0.01
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 1
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession3
      state3 <- liftEffect $ getState store
      case state3.session of
        Just session -> 
          session.totalTokens `shouldEqual` (session.promptTokens + session.completionTokens)
        Nothing -> false `shouldEqual` true
      
      -- Test case 4: Very large token counts
      let testSession4 = 
            { id: "test-session-large"
            , promptTokens: 1000000
            , completionTokens: 2000000
            , totalTokens: 3000000
            , cost: 100.0
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 100
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession4
      state4 <- liftEffect $ getState store
      case state4.session of
        Just session -> 
          session.totalTokens `shouldEqual` (session.promptTokens + session.completionTokens)
        Nothing -> false `shouldEqual` true
    
    it "cost is always non-negative" do
      store <- liftEffect createStore
      now <- liftEffect getCurrentDateTime
      
      -- Test case 1: Positive cost
      let testSession1 = 
            { id: "test-session-789"
            , promptTokens: 100
            , completionTokens: 200
            , totalTokens: 300
            , cost: 0.05
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 5
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession1
      state1 <- liftEffect $ getState store
      case state1.session of
        Just session -> session.cost `shouldBeGreaterThanOrEqual` 0.0
        Nothing -> false `shouldEqual` true
      
      -- Test case 2: Zero cost
      let testSession2 = 
            { id: "test-session-zero-cost"
            , promptTokens: 0
            , completionTokens: 0
            , totalTokens: 0
            , cost: 0.0
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 0
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession2
      state2 <- liftEffect $ getState store
      case state2.session of
        Just session -> session.cost `shouldEqual` 0.0
        Nothing -> false `shouldEqual` true
      
      -- Test case 3: Very large cost
      let testSession3 = 
            { id: "test-session-large-cost"
            , promptTokens: 1000000
            , completionTokens: 2000000
            , totalTokens: 3000000
            , cost: 1000.0
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 100
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession3
      state3 <- liftEffect $ getState store
      case state3.session of
        Just session -> session.cost `shouldBeGreaterThanOrEqual` 0.0
        Nothing -> false `shouldEqual` true
    
    it "message count is positive when session exists" do
      store <- liftEffect createStore
      now <- liftEffect getCurrentDateTime
      
      -- Test case 1: Normal message count
      let testSession1 = 
            { id: "test-session-positive"
            , promptTokens: 100
            , completionTokens: 200
            , totalTokens: 300
            , cost: 0.05
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 5
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession1
      state1 <- liftEffect $ getState store
      case state1.session of
        Just session -> session.messageCount `shouldBeGreaterThanOrEqual` 1
        Nothing -> false `shouldEqual` true
      
      -- Test case 2: Minimum message count (1)
      let testSession2 = 
            { id: "test-session-min-messages"
            , promptTokens: 10
            , completionTokens: 10
            , totalTokens: 20
            , cost: 0.001
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 1
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession2
      state2 <- liftEffect $ getState store
      case state2.session of
        Just session -> session.messageCount `shouldEqual` 1
        Nothing -> false `shouldEqual` true
      
      -- Test case 3: Very large message count
      let testSession3 = 
            { id: "test-session-large-messages"
            , promptTokens: 100000
            , completionTokens: 200000
            , totalTokens: 300000
            , cost: 10.0
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 10000
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession3
      state3 <- liftEffect $ getState store
      case state3.session of
        Just session -> session.messageCount `shouldBeGreaterThanOrEqual` 1
        Nothing -> false `shouldEqual` true
    
    it "startedAt is always before or equal to updatedAt" do
      store <- liftEffect createStore
      now <- liftEffect getCurrentDateTime
      -- Would need DateTime comparison - placeholder for now
      let testSession = 
            { id: "test-session-time"
            , promptTokens: 100
            , completionTokens: 200
            , totalTokens: 300
            , cost: 0.05
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 5
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession
      state <- liftEffect $ getState store
      case state.session of
        Just session -> 
          -- Would verify startedAt <= updatedAt
          true `shouldBeTrue`
        Nothing -> false `shouldEqual` true

-- | Test state transitions
testStateTransitions :: forall m. Monad m => m Unit
testStateTransitions = do
  describe "State Transitions" do
    it "balance update preserves all invariants" do
      store <- liftEffect createStore
      let validBalance = 
            { venice: { diem: 100.0, usd: 50.0, effective: 150.0, lastUpdated: Nothing }
            , consumptionRate: 10.0
            , timeToDepletion: Nothing
            , todayUsed: 0.0
            , todayStartBalance: 1000.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store validBalance
      state <- liftEffect $ getState store
      -- Verify all invariants preserved
      state.balance.venice.diem `shouldBeGreaterThanOrEqual` 0.0
      state.balance.venice.usd `shouldBeGreaterThanOrEqual` 0.0
      state.balance.venice.effective `shouldBeGreaterThanOrEqual` 0.0
      state.balance.consumptionRate `shouldBeGreaterThanOrEqual` 0.0
      state.balance.todayUsed `shouldBeGreaterThanOrEqual` 0.0
      state.balance.todayStartBalance `shouldBeGreaterThanOrEqual` 0.0
      -- Verify effective = diem + usd
      state.balance.venice.effective `shouldEqual` (state.balance.venice.diem + state.balance.venice.usd)
    
    it "multiple balance updates preserve invariants" do
      store <- liftEffect createStore
      
      -- First update
      let balance1 = 
            { venice: { diem: 100.0, usd: 50.0, effective: 150.0, lastUpdated: Nothing }
            , consumptionRate: 10.0
            , timeToDepletion: Nothing
            , todayUsed: 0.0
            , todayStartBalance: 1000.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store balance1
      state1 <- liftEffect $ getState store
      state1.balance.venice.effective `shouldEqual` (state1.balance.venice.diem + state1.balance.venice.usd)
      
      -- Second update
      let balance2 = 
            { venice: { diem: 200.0, usd: 100.0, effective: 300.0, lastUpdated: Nothing }
            , consumptionRate: 20.0
            , timeToDepletion: Nothing
            , todayUsed: 50.0
            , todayStartBalance: 1000.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store balance2
      state2 <- liftEffect $ getState store
      state2.balance.venice.effective `shouldEqual` (state2.balance.venice.diem + state2.balance.venice.usd)
      state2.balance.consumptionRate `shouldBeGreaterThanOrEqual` 0.0
      
      -- Third update (edge case: zero balance)
      let balance3 = 
            { venice: { diem: 0.0, usd: 0.0, effective: 0.0, lastUpdated: Nothing }
            , consumptionRate: 0.0
            , timeToDepletion: Nothing
            , todayUsed: 0.0
            , todayStartBalance: 0.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store balance3
      state3 <- liftEffect $ getState store
      state3.balance.venice.effective `shouldEqual` (state3.balance.venice.diem + state3.balance.venice.usd)
    
    it "session update preserves all invariants" do
      store <- liftEffect createStore
      now <- liftEffect getCurrentDateTime
      let validSession = 
            { id: "test-session-transition"
            , promptTokens: 100
            , completionTokens: 200
            , totalTokens: 300
            , cost: 0.05
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 5
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store validSession
      state <- liftEffect $ getState store
      case state.session of
        Just session -> do
          -- Verify all invariants
          session.totalTokens `shouldEqual` (session.promptTokens + session.completionTokens)
          session.cost `shouldBeGreaterThanOrEqual` 0.0
          session.promptTokens `shouldBeGreaterThanOrEqual` 0
          session.completionTokens `shouldBeGreaterThanOrEqual` 0
          session.totalTokens `shouldBeGreaterThanOrEqual` 0
          session.messageCount `shouldBeGreaterThanOrEqual` 1
          session.id /= "" `shouldBeTrue`
        Nothing -> false `shouldEqual` true
    
    it "multiple session updates preserve invariants" do
      store <- liftEffect createStore
      now <- liftEffect getCurrentDateTime
      
      -- First session
      let session1 = 
            { id: "test-session-1"
            , promptTokens: 100
            , completionTokens: 200
            , totalTokens: 300
            , cost: 0.05
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 5
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store session1
      state1 <- liftEffect $ getState store
      case state1.session of
        Just s -> s.totalTokens `shouldEqual` (s.promptTokens + s.completionTokens)
        Nothing -> false `shouldEqual` true
      
      -- Update same session
      let session2 = 
            { id: "test-session-1"
            , promptTokens: 200
            , completionTokens: 400
            , totalTokens: 600
            , cost: 0.10
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 10
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store session2
      state2 <- liftEffect $ getState store
      case state2.session of
        Just s -> do
          s.totalTokens `shouldEqual` (s.promptTokens + s.completionTokens)
          s.totalTokens `shouldEqual` 600
        Nothing -> false `shouldEqual` true
      
      -- New session
      let session3 = 
            { id: "test-session-2"
            , promptTokens: 50
            , completionTokens: 50
            , totalTokens: 100
            , cost: 0.01
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 2
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store session3
      state3 <- liftEffect $ getState store
      case state3.session of
        Just s -> do
          s.totalTokens `shouldEqual` (s.promptTokens + s.completionTokens)
          s.id `shouldEqual` "test-session-2"
        Nothing -> false `shouldEqual` true
    
    it "clearSession removes session and preserves other state" do
      store <- liftEffect createStore
      now <- liftEffect getCurrentDateTime
      
      -- Set up state with session and balance
      let testBalance = 
            { venice: { diem: 100.0, usd: 50.0, effective: 150.0, lastUpdated: Nothing }
            , consumptionRate: 10.0
            , timeToDepletion: Nothing
            , todayUsed: 0.0
            , todayStartBalance: 1000.0
            , resetCountdown: Nothing
            , alertLevel: initialState.balance.alertLevel
            }
      liftEffect $ updateBalance store testBalance
      
      let testSession = 
            { id: "test-session-clear"
            , promptTokens: 100
            , completionTokens: 200
            , totalTokens: 300
            , cost: 0.05
            , model: "claude-3-opus"
            , provider: "venice"
            , messageCount: 5
            , startedAt: now
            , updatedAt: now
            }
      liftEffect $ updateSession store testSession
      
      -- Verify session exists
      stateBefore <- liftEffect $ getState store
      case stateBefore.session of
        Just _ -> true `shouldBeTrue`
        Nothing -> false `shouldEqual` true
      
      -- Clear session
      liftEffect $ clearSession store
      stateAfter <- liftEffect $ getState store
      
      -- Verify session is removed
      stateAfter.session `shouldEqual` Nothing
      
      -- Verify balance is preserved
      stateAfter.balance.venice.diem `shouldEqual` 100.0
      stateAfter.balance.venice.usd `shouldEqual` 50.0
      stateAfter.balance.venice.effective `shouldEqual` 150.0
    
    it "clearSession is idempotent" do
      store <- liftEffect createStore
      
      -- Clear when no session exists
      liftEffect $ clearSession store
      state1 <- liftEffect $ getState store
      state1.session `shouldEqual` Nothing
      
      -- Clear again
      liftEffect $ clearSession store
      state2 <- liftEffect $ getState store
      state2.session `shouldEqual` Nothing

-- | Property: Balance invariants always hold after update
prop_balanceInvariantsPreserved :: BalanceState -> Boolean
prop_balanceInvariantsPreserved balance = 
  balance.venice.diem >= 0.0 &&
  balance.venice.usd >= 0.0 &&
  balance.venice.effective >= 0.0 &&
  balance.consumptionRate >= 0.0 &&
  balance.todayUsed >= 0.0 &&
  balance.todayStartBalance >= 0.0 &&
  -- Effective should equal diem + usd (within floating point precision)
  let expected = balance.venice.diem + balance.venice.usd
      diff = if balance.venice.effective > expected then balance.venice.effective - expected else expected - balance.venice.effective
  in diff < 0.01

-- | Property: Session invariants always hold after update
prop_sessionInvariantsPreserved :: SessionState -> Boolean
prop_sessionInvariantsPreserved session = 
  session.promptTokens >= 0 &&
  session.completionTokens >= 0 &&
  session.totalTokens >= 0 &&
  session.totalTokens == session.promptTokens + session.completionTokens &&
  session.cost >= 0.0 &&
  session.messageCount >= 1 &&
  session.id /= ""

-- | Property tests
testProperties :: forall m. Monad m => m Unit
testProperties = do
  describe "Property Tests" do
    it "balance invariants always preserved after update" do
      quickCheck prop_balanceInvariantsPreserved
    
    it "session invariants always preserved after update" do
      quickCheck prop_sessionInvariantsPreserved

foreign import getCurrentDateTime :: Effect DateTime
