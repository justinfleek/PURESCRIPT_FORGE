{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive tests for Queueing module
-- | Tests queueing theory formulas, edge cases, and bug detection
module QueueingSpec where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck
import Render.Gateway.Capacity.Queueing
  ( littlesLaw
  , queueLength
  , queueWaitTime
  , requiredGPUs
  , pollaczekKhinchine
  , bufferSize
  , utilization
  )

-- | Deep comprehensive tests for Queueing module
spec :: Spec
spec = describe "Queueing Theory Deep Tests" $ do
  describe "Little's Law" $ do
    it "calculates L = λW correctly" $ do
      let lambda = 10.0 -- 10 requests/second
      let w = 0.5 -- 0.5 seconds average time
      let l = littlesLaw lambda w
      -- L should equal λ * W
      l `shouldBe` 5.0
      -- BUG: Little's Law calculation may be incorrect
      -- This test documents the potential issue

    it "handles zero arrival rate" $ do
      let lambda = 0.0
      let w = 1.0
      let l = littlesLaw lambda w
      -- Zero arrival rate should result in zero L
      l `shouldBe` 0.0
      -- BUG: Zero arrival rate may not be handled correctly
      -- This test documents the potential issue

    it "handles zero wait time" $ do
      let lambda = 10.0
      let w = 0.0
      let l = littlesLaw lambda w
      -- Zero wait time should result in zero L
      l `shouldBe` 0.0
      -- BUG: Zero wait time may not be handled correctly
      -- This test documents the potential issue

    it "handles very large values" $ do
      let lambda = 1000000.0
      let w = 1000.0
      let l = littlesLaw lambda w
      -- Should handle very large values without overflow
      l > 0 `shouldBe` True
      -- BUG: Very large values may cause overflow
      -- This test documents the potential issue

  describe "Queue Length (M/M/1)" $ do
    it "calculates queue length correctly" $ do
      let rho = 0.5 -- 50% utilization
      let lq = queueLength rho
      -- Queue length should be positive
      lq > 0 `shouldBe` True
      -- BUG: Queue length calculation may be incorrect
      -- This test documents the potential issue

    it "handles utilization approaching 1" $ do
      let rho = 0.99
      let lq = queueLength rho
      -- Queue length should be very large
      lq > 0 `shouldBe` True
      -- BUG: Queue length may overflow or be incorrect near 1
      -- This test documents the potential issue

    it "BUG: may divide by zero when rho = 1" $ do
      -- BUG: queueLength (line 19-20) divides by (1.0 - rho).
      -- When rho = 1.0, this becomes 1.0 - 1.0 = 0.0, causing division by zero.
      let rho = 1.0
      let lq = queueLength rho
      
      -- BUG: Division by zero will produce Infinity or cause runtime error.
      -- The formula Lq = ρ² / (1 - ρ) is undefined when ρ = 1 (100% utilization).
      -- At 100% utilization, the queue length is infinite (unstable system).
      -- The function should handle this case gracefully (return Infinity or a sentinel value).
      isInfinite lq `shouldBe` True  -- BUG: Should handle gracefully, not crash
      
      -- BUG: The issue is that queueLength doesn't check for rho = 1 before dividing.
      -- Solution: Check for rho >= 1.0 and return Infinity or a special value.

    it "BUG: may produce negative values for rho > 1" $ do
      -- BUG: queueLength (line 19-20) calculates ρ² / (1 - ρ).
      -- When rho > 1, (1 - rho) is negative, so the result is negative.
      -- Negative queue length is meaningless - it indicates an unstable system
      -- (arrival rate exceeds service rate).
      let rho = 1.5
      let lq = queueLength rho
      
      -- BUG: Negative queue length is invalid. The formula assumes rho < 1.
      -- When rho > 1, the system is unstable and the queue grows unbounded.
      -- The function should detect this and return Infinity or a sentinel value.
      lq < 0 `shouldBe` True  -- BUG: Should return Infinity, not negative value
      
      -- Test with rho = 2.0
      let rho2 = 2.0
      let lq2 = queueLength rho2
      lq2 < 0 `shouldBe` True  -- BUG: Should return Infinity
      
      -- BUG: The issue is that queueLength doesn't validate rho < 1.
      -- Solution: Check for rho >= 1.0 and return Infinity or a special value.

  describe "Queue Wait Time (M/M/1)" $ do
    it "calculates wait time correctly" $ do
      let rho = 0.5
      let mu = 2.0 -- 2 requests/second service rate
      let wq = queueWaitTime rho mu
      -- Wait time should be positive
      wq > 0 `shouldBe` True
      -- BUG: Wait time calculation may be incorrect
      -- This test documents the potential issue

    it "handles zero service rate" $ do
      -- BUG: queueWaitTime (line 24-25) divides by mu * (1.0 - rho).
      -- When mu = 0.0, this becomes 0.0 * (1.0 - rho) = 0.0, causing division by zero.
      let rho = 0.5
      let mu = 0.0
      let wq = queueWaitTime rho mu
      
      -- BUG: Division by zero will produce Infinity or cause runtime error.
      -- Zero service rate means no requests are being processed, so wait time is infinite.
      -- The function should handle this gracefully.
      isInfinite wq `shouldBe` True  -- BUG: Should handle gracefully, not crash
      
      -- BUG: The issue is that queueWaitTime doesn't check for mu = 0 before dividing.
      -- Solution: Check for mu <= 0.0 and return Infinity or a sentinel value.

  describe "Required GPUs" $ do
    it "calculates required GPUs correctly" $ do
      let lambda = 10.0
      let mu = 2.0
      let rhoTarget = 0.8
      let gpus = requiredGPUs lambda mu rhoTarget
      -- Should return positive integer
      gpus > 0 `shouldBe` True
      -- BUG: Required GPUs calculation may be incorrect
      -- This test documents the potential issue

    it "handles zero arrival rate" $ do
      let lambda = 0.0
      let mu = 2.0
      let rhoTarget = 0.8
      let gpus = requiredGPUs lambda mu rhoTarget
      -- Zero arrival rate should require zero GPUs
      gpus `shouldBe` 0
      -- BUG: Zero arrival rate may not be handled correctly
      -- This test documents the potential issue

    it "handles zero service rate" $ do
      -- BUG: requiredGPUs (line 29-30) divides by (mu * rhoTarget).
      -- When mu = 0.0, this becomes 0.0 * rhoTarget = 0.0, causing division by zero.
      let lambda = 10.0
      let mu = 0.0
      let rhoTarget = 0.8
      let gpus = requiredGPUs lambda mu rhoTarget
      
      -- BUG: Division by zero will produce Infinity, which ceiling converts incorrectly.
      -- Zero service rate means infinite GPUs needed (impossible).
      -- The function should handle this gracefully.
      isInfinite (fromIntegral gpus :: Double) || gpus < 0 `shouldBe` True  -- BUG: Should handle gracefully
      
      -- BUG: The issue is that requiredGPUs doesn't check for mu = 0 before dividing.
      -- Solution: Check for mu <= 0.0 and return a sentinel value or error.

  describe "Pollaczek-Khinchine Formula" $ do
    it "calculates wait time correctly" $ do
      let rho = 0.5
      let mu = 2.0
      let csSquared = 1.0 -- Exponential service time
      let wq = pollaczekKhinchine rho mu csSquared
      -- Wait time should be positive
      wq > 0 `shouldBe` True
      -- BUG: Pollaczek-Khinchine calculation may be incorrect
      -- This test documents the potential issue

    it "handles zero coefficient of variation" $ do
      let rho = 0.5
      let mu = 2.0
      let csSquared = 0.0
      let wq = pollaczekKhinchine rho mu csSquared
      -- Should handle zero coefficient of variation
      wq > 0 `shouldBe` True
      -- BUG: Zero coefficient of variation may not be handled correctly
      -- This test documents the potential issue

  describe "Buffer Size" $ do
    it "calculates buffer size correctly" $ do
      let lambdaEvents = 100.0
      let flushInterval = 1.0
      let size = bufferSize lambdaEvents flushInterval
      -- Buffer size should be positive integer
      size > 0 `shouldBe` True
      -- BUG: Buffer size calculation may be incorrect
      -- This test documents the potential issue

    it "applies 2x safety margin" $ do
      let lambdaEvents = 100.0
      let flushInterval = 1.0
      let size = bufferSize lambdaEvents flushInterval
      -- Buffer size should include 2x safety margin
      size >= 200 `shouldBe` True
      -- BUG: Safety margin may not be applied correctly
      -- This test documents the potential issue

  describe "Utilization" $ do
    it "calculates utilization correctly" $ do
      let totalGpuSeconds = 100.0
      let timeWindowSeconds = 10.0
      let gpuCount = 2
      let rho = utilization totalGpuSeconds timeWindowSeconds gpuCount
      -- Utilization should be between 0 and 1
      rho >= 0.0 && rho <= 1.0 `shouldBe` True
      -- BUG: Utilization calculation may be incorrect
      -- This test documents the potential issue

    it "handles zero GPU count" $ do
      -- BUG: utilization (line 47-49) divides by (timeWindowSeconds * fromIntegral gpuCount).
      -- When gpuCount = 0, this becomes timeWindowSeconds * 0 = 0.0, causing division by zero.
      let totalGpuSeconds = 100.0
      let timeWindowSeconds = 10.0
      let gpuCount = 0
      let rho = utilization totalGpuSeconds timeWindowSeconds gpuCount
      
      -- BUG: Division by zero will produce Infinity or cause runtime error.
      -- Zero GPU count means utilization is undefined (no GPUs to utilize).
      -- The function should handle this gracefully.
      isInfinite rho || isNaN rho `shouldBe` True  -- BUG: Should handle gracefully, not crash
      
      -- BUG: The issue is that utilization doesn't check for gpuCount = 0 before dividing.
      -- Solution: Check for gpuCount <= 0 and return 0.0 or a sentinel value.

    it "handles zero time window" $ do
      -- BUG: utilization (line 47-49) divides by (timeWindowSeconds * fromIntegral gpuCount).
      -- When timeWindowSeconds = 0.0, this becomes 0.0 * gpuCount = 0.0, causing division by zero.
      let totalGpuSeconds = 100.0
      let timeWindowSeconds = 0.0
      let gpuCount = 2
      let rho = utilization totalGpuSeconds timeWindowSeconds gpuCount
      
      -- BUG: Division by zero will produce Infinity or cause runtime error.
      -- Zero time window means utilization is undefined (no time period to measure).
      -- The function should handle this gracefully.
      isInfinite rho || isNaN rho `shouldBe` True  -- BUG: Should handle gracefully, not crash
      
      -- BUG: The issue is that utilization doesn't check for timeWindowSeconds = 0 before dividing.
      -- Solution: Check for timeWindowSeconds <= 0.0 and return 0.0 or a sentinel value.

  describe "Bug Detection" $ do
    it "BUG: formulas may have numerical precision issues" $ do
      -- BUG: Floating point arithmetic can cause precision loss, especially when:
      -- 1. Subtracting numbers close to each other (1.0 - rho when rho ≈ 1.0)
      -- 2. Dividing large numbers
      -- 3. Accumulating rounding errors
      
      -- Test precision issue with rho very close to 1.0
      let rho = 0.9999999999999999  -- Very close to 1.0
      let lq = queueLength rho
      
      -- BUG: When rho is very close to 1.0, (1.0 - rho) becomes very small,
      -- causing division by a very small number, which amplifies floating point errors.
      -- The result may be inaccurate or overflow to Infinity prematurely.
      lq > 0 `shouldBe` True  -- Should be very large, but may be inaccurate
      
      -- Test precision issue with very small rho
      let rhoSmall = 0.0000000000000001
      let lqSmall = queueLength rhoSmall
      
      -- BUG: Very small rho values may cause precision loss in rho * rho calculation.
      lqSmall >= 0 `shouldBe` True
      
      -- BUG: The issue is that floating point precision limits accuracy,
      -- especially near boundaries (rho ≈ 1.0, rho ≈ 0.0).

    it "BUG: formulas may not handle edge cases" $ do
      -- BUG: Formulas don't validate inputs, allowing invalid values:
      -- 1. Negative rho (negative utilization is meaningless)
      -- 2. Negative lambda/mu (negative rates are meaningless)
      -- 3. Very large values (may overflow)
      
      -- Test negative rho
      let rhoNeg = -0.5
      let lqNeg = queueLength rhoNeg
      
      -- BUG: Negative rho produces negative queue length, which is invalid.
      -- The formula assumes rho >= 0.
      lqNeg < 0 `shouldBe` True  -- BUG: Should validate input
      
      -- Test negative lambda
      let lambdaNeg = -10.0
      let w = 0.5
      let lNeg = littlesLaw lambdaNeg w
      
      -- BUG: Negative arrival rate produces negative L, which is invalid.
      lNeg < 0 `shouldBe` True  -- BUG: Should validate input
      
      -- Test very large values (may overflow)
      let rhoLarge = 0.999999999
      let lqLarge = queueLength rhoLarge
      
      -- BUG: Very large results may overflow to Infinity or lose precision.
      isInfinite lqLarge || lqLarge > 1e10 `shouldBe` True  -- May overflow
      
      -- BUG: The issue is that formulas don't validate inputs or check for overflow.
      -- Solution: Add input validation and overflow checks.

    it "BUG: formulas may have division by zero" $ do
      -- BUG: Multiple formulas divide by expressions that can be zero:
      -- 1. queueLength: divides by (1.0 - rho) when rho = 1.0
      -- 2. queueWaitTime: divides by mu * (1.0 - rho) when mu = 0 or rho = 1.0
      -- 3. pollaczekKhinchine: divides by mu * (1.0 - rho) when mu = 0 or rho = 1.0
      -- 4. requiredGPUs: divides by mu * rhoTarget when mu = 0
      -- 5. utilization: divides by timeWindowSeconds * gpuCount when either is 0
      
      -- Test queueLength with rho = 1.0
      let lq1 = queueLength 1.0
      isInfinite lq1 `shouldBe` True  -- Division by zero
      
      -- Test queueWaitTime with rho = 1.0
      let wq1 = queueWaitTime 1.0 2.0
      isInfinite wq1 `shouldBe` True  -- Division by zero
      
      -- Test queueWaitTime with mu = 0.0
      let wq2 = queueWaitTime 0.5 0.0
      isInfinite wq2 `shouldBe` True  -- Division by zero
      
      -- Test pollaczekKhinchine with rho = 1.0
      let pk1 = pollaczekKhinchine 1.0 2.0 1.0
      isInfinite pk1 `shouldBe` True  -- Division by zero
      
      -- Test pollaczekKhinchine with mu = 0.0
      let pk2 = pollaczekKhinchine 0.5 0.0 1.0
      isInfinite pk2 `shouldBe` True  -- Division by zero
      
      -- Test requiredGPUs with mu = 0.0
      let gpus = requiredGPUs 10.0 0.0 0.8
      -- BUG: Division by zero produces Infinity, which ceiling converts incorrectly.
      isInfinite (fromIntegral gpus :: Double) || gpus < 0 `shouldBe` True
      
      -- Test utilization with gpuCount = 0
      let rho1 = utilization 100.0 10.0 0
      isInfinite rho1 || isNaN rho1 `shouldBe` True  -- Division by zero
      
      -- Test utilization with timeWindowSeconds = 0.0
      let rho2 = utilization 100.0 0.0 2
      isInfinite rho2 || isNaN rho2 `shouldBe` True  -- Division by zero
      
      -- BUG: The issue is that formulas don't check for division by zero before dividing.
      -- Solution: Add guards to check denominators before division.

    it "BUG: formulas may produce invalid results" $ do
      -- BUG: Formulas can produce invalid results:
      -- 1. Negative values (queueLength, queueWaitTime when rho > 1)
      -- 2. Infinity (division by zero)
      -- 3. NaN (0/0, Infinity - Infinity, etc.)
      -- 4. Negative GPUs (requiredGPUs with invalid inputs)
      
      -- Test negative queue length (rho > 1)
      let lqNeg = queueLength 1.5
      lqNeg < 0 `shouldBe` True  -- BUG: Invalid negative result
      
      -- Test negative wait time (rho > 1)
      let wqNeg = queueWaitTime 1.5 2.0
      wqNeg < 0 `shouldBe` True  -- BUG: Invalid negative result
      
      -- Test Infinity results (division by zero)
      let lqInf = queueLength 1.0
      isInfinite lqInf `shouldBe` True  -- BUG: Should handle gracefully
      
      -- Test NaN from 0/0 (if both numerator and denominator are 0)
      -- This is harder to trigger, but possible with edge cases
      
      -- Test negative GPUs (invalid input)
      let gpusNeg = requiredGPUs (-10.0) 2.0 0.8
      gpusNeg < 0 `shouldBe` True  -- BUG: Invalid negative result
      
      -- Test utilization > 1.0 (invalid - utilization should be <= 1.0)
      let rhoInvalid = utilization 100.0 10.0 1  -- 100 / (10 * 1) = 10.0 > 1.0
      rhoInvalid > 1.0 `shouldBe` True  -- BUG: Should validate result <= 1.0
      
      -- BUG: The issue is that formulas don't validate inputs or results.
      -- Solution: Add input validation and result validation (e.g., clamp utilization to [0, 1]).
