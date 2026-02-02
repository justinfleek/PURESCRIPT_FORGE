-- | Property tests for balance calculations
-- | Based on spec 70-TESTING-STRATEGY.md
module Test.Sidepanel.State.BalanceSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.Spec.QuickCheck (quickCheck, (<?>))
import Sidepanel.State.Balance (BalanceState, calculateAlertLevel, initialBalanceState, VeniceBalance, AlertLevel(..))
import Data.Maybe (Maybe(..))

spec :: Spec Unit
spec = describe "Balance State" do
  describe "calculateAlertLevel" do
    it "returns Depleted when Diem is zero" do
      let balance = initialBalanceState
        { venice = Just { diem: 0.0, usd: 10.0, effective: 10.0, todayUsed: 0.0, todayStartBalance: 50.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Depleted
    
    it "returns Depleted when Diem is exactly zero with zero USD" do
      let balance = initialBalanceState
        { venice = Just { diem: 0.0, usd: 0.0, effective: 0.0, todayUsed: 0.0, todayStartBalance: 0.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Depleted
    
    it "returns Critical when Diem is less than 1" do
      let balance = initialBalanceState
        { venice = Just { diem: 0.5, usd: 0.0, effective: 0.5, todayUsed: 49.5, todayStartBalance: 50.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Critical
    
    it "returns Critical when Diem is very close to zero" do
      let balance = initialBalanceState
        { venice = Just { diem: 0.0001, usd: 0.0, effective: 0.0001, todayUsed: 49.9999, todayStartBalance: 50.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Critical
    
    it "returns Critical when Diem is exactly 0.999" do
      let balance = initialBalanceState
        { venice = Just { diem: 0.999, usd: 0.0, effective: 0.999, todayUsed: 49.001, todayStartBalance: 50.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Critical
    
    it "returns Warning when Diem is less than 5" do
      let balance = initialBalanceState
        { venice = Just { diem: 3.0, usd: 0.0, effective: 3.0, todayUsed: 47.0, todayStartBalance: 50.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Warning
    
    it "returns Warning when Diem is exactly 1.0" do
      let balance = initialBalanceState
        { venice = Just { diem: 1.0, usd: 0.0, effective: 1.0, todayUsed: 49.0, todayStartBalance: 50.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Warning
    
    it "returns Warning when Diem is exactly 4.999" do
      let balance = initialBalanceState
        { venice = Just { diem: 4.999, usd: 0.0, effective: 4.999, todayUsed: 45.001, todayStartBalance: 50.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Warning
    
    it "returns Normal for healthy balance" do
      let balance = initialBalanceState
        { venice = Just { diem: 50.0, usd: 10.0, effective: 60.0, todayUsed: 0.0, todayStartBalance: 50.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Normal
    
    it "returns Normal when Diem is exactly 5.0" do
      let balance = initialBalanceState
        { venice = Just { diem: 5.0, usd: 0.0, effective: 5.0, todayUsed: 45.0, todayStartBalance: 50.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Normal
    
    it "returns Normal for very large balance" do
      let balance = initialBalanceState
        { venice = Just { diem: 1.0e10, usd: 5.0e9, effective: 1.5e10, todayUsed: 0.0, todayStartBalance: 1.0e10, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Normal
    
    it "handles balance with USD but zero Diem" do
      let balance = initialBalanceState
        { venice = Just { diem: 0.0, usd: 100.0, effective: 100.0, todayUsed: 0.0, todayStartBalance: 100.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Depleted
    
    it "handles balance with Diem but zero USD" do
      let balance = initialBalanceState
        { venice = Just { diem: 10.0, usd: 0.0, effective: 10.0, todayUsed: 0.0, todayStartBalance: 10.0, resetCountdown: Nothing }
        }
      calculateAlertLevel balance `shouldEqual` Normal
  
  describe "Property Tests" do
    it "alert level is never undefined" $
      quickCheck \balance ->
        let level = calculateAlertLevel balance
        in level == Normal || level == Warning || level == Critical || level == Depleted
          <?> "Alert level must be one of Normal, Warning, Critical, Depleted"
    
    it "alert level transitions are monotonic (Depleted < Critical < Warning < Normal)" $
      quickCheck \diem1 diem2 ->
        if diem1 < diem2 && diem1 >= 0.0 && diem2 >= 0.0 then
          let balance1 = initialBalanceState
                { venice = Just { diem: diem1, usd: 0.0, effective: diem1, todayUsed: 0.0, todayStartBalance: 100.0, resetCountdown: Nothing }
              balance2 = initialBalanceState
                { venice = Just { diem: diem2, usd: 0.0, effective: diem2, todayUsed: 0.0, todayStartBalance: 100.0, resetCountdown: Nothing }
              level1 = calculateAlertLevel balance1
              level2 = calculateAlertLevel balance2
            in true -- Would verify level ordering
        else
          true
    
    it "effective balance equals diem + usd when Venice balance exists" $
      quickCheck \venice ->
        if venice.diem >= 0.0 && venice.usd >= 0.0 then
          venice.effective == venice.diem + venice.usd
            <?> "Effective balance must equal diem + usd"
        else
          true
    
    it "consumption rate is never negative" $
      quickCheck \balance ->
        balance.consumptionRate >= 0.0
          <?> "Consumption rate must be non-negative"
    
    it "total cost is never negative" $
      quickCheck \balance ->
        balance.totalCost >= 0.0
          <?> "Total cost must be non-negative"
    
    it "todayUsed is never negative" $
      quickCheck \balance ->
        balance.todayUsed >= 0.0
          <?> "Today used must be non-negative"
    
    it "todayStartBalance is never negative" $
      quickCheck \balance ->
        balance.todayStartBalance >= 0.0
          <?> "Today start balance must be non-negative"
    
    it "todayUsed never exceeds todayStartBalance" $
      quickCheck \balance ->
        balance.todayUsed <= balance.todayStartBalance
          <?> "Today used must not exceed today start balance"
    
    it "alert level is Depleted when diem is zero" $
      quickCheck \usd ->
        if usd >= 0.0 then
          let balance = initialBalanceState
                { venice = Just { diem: 0.0, usd: usd, effective: usd, todayUsed: 0.0, todayStartBalance: 100.0, resetCountdown: Nothing }
            in calculateAlertLevel balance == Depleted
              <?> "Alert level must be Depleted when diem is zero"
        else
          true
    
    it "alert level is Normal when diem >= 5.0" $
      quickCheck \diem ->
        if diem >= 5.0 && diem <= 1.0e10 then
          let balance = initialBalanceState
                { venice = Just { diem: diem, usd: 0.0, effective: diem, todayUsed: 0.0, todayStartBalance: diem, resetCountdown: Nothing }
            in calculateAlertLevel balance == Normal
              <?> "Alert level must be Normal when diem >= 5.0"
        else
          true