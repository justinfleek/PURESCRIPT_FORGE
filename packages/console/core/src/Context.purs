-- | Context Module
-- |
-- | Provides request-scoped context using Reader monad transformer.
-- | Pure functional context propagation without mutable state.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/context.ts
module Forge.Console.Core.Context
  ( Context
  , ContextT
  , NotFoundError(..)
  , runContext
  , askContext
  , localContext
  ) where

import Prelude

import Control.Monad.Reader.Trans (ReaderT, runReaderT)
import Control.Monad.Reader.Class (class MonadReader, ask, local)
import Data.Either (Either(..))

-- | Error when context is accessed but not provided
data NotFoundError = NotFoundError

derive instance eqNotFoundError :: Eq NotFoundError

instance showNotFoundError :: Show NotFoundError where
  show NotFoundError = "Context.NotFoundError: Context not found"

-- | Context type alias - the value being threaded through computation
type Context a = a

-- | Context monad transformer
-- | Threads context through computations using Reader
type ContextT ctx m = ReaderT ctx m

-- | Run a computation with provided context
runContext :: forall ctx m a. ctx -> ContextT ctx m a -> m a
runContext ctx computation = runReaderT computation ctx

-- | Access the current context value
askContext :: forall ctx m. MonadReader ctx m => m ctx
askContext = ask

-- | Modify the context for a sub-computation
localContext :: forall ctx m a. MonadReader ctx m => (ctx -> ctx) -> m a -> m a
localContext = local
