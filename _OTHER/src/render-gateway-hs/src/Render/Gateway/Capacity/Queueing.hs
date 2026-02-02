{-# LANGUAGE StrictData #-}

-- | Render Gateway Queueing Theory
-- | Capacity planning formulas per render_specs.pdf §12
module Render.Gateway.Capacity.Queueing where

import Prelude hiding (head, tail)

-- | Little's Law: L = λW
-- | L = average number of requests in system
-- | λ = arrival rate (requests/second)
-- | W = average time in system
littlesLaw :: Double -> Double -> Double
littlesLaw lambda w = lambda * w

-- | Queue length for M/M/1 queue
-- | Lq = ρ² / (1 - ρ)
-- | ρ = utilization (λ/μ)
queueLength :: Double -> Double
queueLength rho = (rho * rho) / (1.0 - rho)

-- | Queue wait time for M/M/1 queue
-- | Wq = Lq / λ = ρ / (μ(1 - ρ))
queueWaitTime :: Double -> Double -> Double
queueWaitTime rho mu = rho / (mu * (1.0 - rho))

-- | Required GPUs for target utilization
-- | GPUs = ⌈λ / (μ · ρtarget)⌉
requiredGPUs :: Double -> Double -> Double -> Int
requiredGPUs lambda mu rhoTarget = ceiling (lambda / (mu * rhoTarget))

-- | Pollaczek-Khinchine formula for M/G/k queue
-- | Wq = ρ(1 + C²s) / (2μ(1 - ρ))
-- | C²s = squared coefficient of variation of service time
pollaczekKhinchine :: Double -> Double -> Double -> Double
pollaczekKhinchine rho mu csSquared = 
  (rho * (1.0 + csSquared)) / (2.0 * mu * (1.0 - rho))

-- | Buffer sizing for STM buffer
-- | Lbuffer = λevents · Wflush
bufferSize :: Double -> Double -> Int
bufferSize lambdaEvents flushInterval = 
  ceiling (lambdaEvents * flushInterval * 2.0) -- 2× safety margin

-- | Utilization from observed metrics
-- | ρ = sum(gpu_seconds) / (time_window * gpu_count)
utilization :: Double -> Double -> Int -> Double
utilization totalGpuSeconds timeWindowSeconds gpuCount = 
  totalGpuSeconds / (timeWindowSeconds * fromIntegral gpuCount)
