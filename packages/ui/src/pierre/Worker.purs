-- | Pierre Worker Pool Management
-- |
-- | Manages Web Worker pools for parallel syntax highlighting in diffs.
-- | Uses a pool of workers to process multiple diffs concurrently.
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/pierre/worker.ts
module Forge.UI.Pierre.Worker
  ( WorkerPoolManager
  , WorkerConfig
  , PoolConfig
  , getWorkerPool
  , getWorkerPools
  , workerFactory
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Forge.UI.Pierre.Types (LineDiffType(..), WorkerPoolStyle(..))

-- | Configuration for individual workers
type WorkerConfig =
  { theme :: String
  , lineDiffType :: LineDiffType
  }

-- | Configuration for the worker pool
type PoolConfig =
  { poolSize :: Int  -- Number of workers in the pool (default: 2 for OpenCode)
  }

-- | Foreign type for the worker pool manager
-- | Wraps the @pierre/diffs WorkerPoolManager
foreign import data WorkerPoolManager :: Type

-- | Create a new Web Worker for syntax highlighting
-- | FFI: Creates a Worker from the @pierre/diffs worker script
foreign import workerFactory :: Effect WorkerPoolManager

-- | Get or create a worker pool for the given style
-- | Returns Nothing on server-side (no window object)
-- | 
-- | - UnifiedPool: Uses "none" line diff type
-- | - SplitPool: Uses "word-alt" line diff type for word-level diffs
foreign import getWorkerPool :: WorkerPoolStyle -> Effect (Maybe WorkerPoolManager)

-- | Get both worker pools
-- | Returns a record with unified and split pools
-- | Either pool may be Nothing on server-side
foreign import getWorkerPools :: Effect { unified :: Maybe WorkerPoolManager, split :: Maybe WorkerPoolManager }
