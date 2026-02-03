-- | Worker Pool Context - Web Worker Management
-- |
-- | Provides access to worker pools for diff rendering.
-- | Supports both unified and split diff styles.
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/context/worker-pool.tsx
module Forge.UI.Context.WorkerPool
  ( WorkerPools
  , WorkerPoolProvider
  , useWorkerPool
  , WorkerPoolManager
  , DiffStyle(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Halogen.HTML as HH

-- | Diff style enum
data DiffStyle
  = Unified
  | Split

derive instance eqDiffStyle :: Eq DiffStyle

-- | Worker pool manager type (opaque FFI type)
foreign import data WorkerPoolManager :: Type

-- | Worker pools configuration
type WorkerPools =
  { unified :: Maybe WorkerPoolManager
  , split :: Maybe WorkerPoolManager
  }

-- | Internal context reference
foreign import workerPoolContextRef :: Ref (Maybe WorkerPools)

-- | Worker pool provider props
type WorkerPoolProviderProps =
  { pools :: WorkerPools
  , children :: Array (HH.HTML Unit Unit)
  }

-- | Worker pool provider component
type WorkerPoolProvider = WorkerPoolProviderProps -> HH.HTML Unit Unit

-- | Use worker pool for the specified diff style
useWorkerPool :: Maybe DiffStyle -> Effect (Maybe WorkerPoolManager)
useWorkerPool mStyle = do
  mPools <- Ref.read workerPoolContextRef
  case mPools of
    Nothing -> throw "WorkerPool context must be used within a WorkerPoolProvider"
    Just pools ->
      case mStyle of
        Just Split -> pure pools.split
        _ -> pure pools.unified
