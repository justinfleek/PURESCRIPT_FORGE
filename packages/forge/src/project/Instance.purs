{-|
Module      : Forge.Project.Instance
Description : Project Instance Management

Manages the lifecycle of project instances. A project instance represents
an active working context with initialized services and state.

== Instance Lifecycle

1. Create instance with configuration
2. Initialize services (LSP, file watchers, etc.)
3. Execute operations within instance
4. Dispose instance (cleanup resources)
-}
module Forge.Project.Instance
  ( -- * Types
    Instance
  , InstanceConfig
  , InstanceState(..)
  , InstanceBootstrap
    -- * Instance Operations
  , create
  , provide
  , dispose
  , getCurrent
    -- * Instance Queries
  , isActive
  , getDirectory
  , getState
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff, try)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Instance state
data InstanceState
  = Initializing
  | Active
  | Disposing
  | Disposed
  | Failed String

derive instance eqInstanceState :: Eq InstanceState

instance showInstanceState :: Show InstanceState where
  show Initializing = "initializing"
  show Active = "active"
  show Disposing = "disposing"
  show Disposed = "disposed"
  show (Failed e) = "failed: " <> e

-- | Instance configuration
type InstanceConfig a =
  { directory :: String
  , init :: Aff Unit           -- Initialization action
  , fn :: Aff a                -- Main action to run
  , cleanup :: Maybe (Aff Unit) -- Optional cleanup action
  }

-- | Project instance
type Instance =
  { id :: String
  , directory :: String
  , state :: InstanceState
  , createdAt :: Number
  , services :: Array String
  }

-- | Bootstrap type alias
type InstanceBootstrap = Unit

-- ============================================================================
-- FFI
-- ============================================================================

foreign import getCurrentInstanceFFI :: Aff (Maybe Instance)
foreign import setCurrentInstanceFFI :: Instance -> Aff Unit
foreign import clearCurrentInstanceFFI :: Aff Unit
foreign import generateIdFFI :: Aff String
foreign import nowFFI :: Aff Number

-- ============================================================================
-- INSTANCE OPERATIONS
-- ============================================================================

{-| Create a new project instance.

Creates an instance but does not initialize it yet.
-}
create :: String -> Aff (Either String Instance)
create directory = do
  instanceId <- generateIdFFI
  now <- nowFFI
  let inst =
        { id: instanceId
        , directory
        , state: Initializing
        , createdAt: now
        , services: []
        }
  pure $ Right inst

{-| Provide an instance and run a computation within it.

Initializes the instance, runs the computation, and cleans up.
-}
provide :: forall a. InstanceConfig a -> Aff (Either String a)
provide config = do
  -- Create instance
  instResult <- create config.directory
  case instResult of
    Left err -> pure $ Left err
    Right inst -> do
      -- Set as current
      setCurrentInstanceFFI inst { state = Initializing }
      
      -- Run initialization
      initResult <- try config.init
      case initResult of
        Left err -> do
          setCurrentInstanceFFI inst { state = Failed (show err) }
          pure $ Left (show err)
        Right _ -> do
          -- Mark as active
          setCurrentInstanceFFI inst { state = Active }
          
          -- Run main function
          fnResult <- try config.fn
          
          -- Cleanup
          case config.cleanup of
            Just cleanup -> do
              _ <- try cleanup
              pure unit
            Nothing -> pure unit
          
          -- Mark as disposed
          setCurrentInstanceFFI inst { state = Disposed }
          clearCurrentInstanceFFI
          
          case fnResult of
            Left err -> pure $ Left (show err)
            Right value -> pure $ Right value

{-| Dispose the current instance.

Cleans up resources and marks instance as disposed.
-}
dispose :: Aff (Either String Unit)
dispose = do
  current <- getCurrentInstanceFFI
  case current of
    Nothing -> pure $ Right unit
    Just inst -> do
      setCurrentInstanceFFI inst { state = Disposing }
      -- In production, would cleanup services here
      setCurrentInstanceFFI inst { state = Disposed }
      clearCurrentInstanceFFI
      pure $ Right unit

{-| Get the current active instance. -}
getCurrent :: Aff (Maybe Instance)
getCurrent = getCurrentInstanceFFI

-- ============================================================================
-- INSTANCE QUERIES
-- ============================================================================

{-| Check if the current instance is active. -}
isActive :: Aff Boolean
isActive = do
  current <- getCurrentInstanceFFI
  pure $ case current of
    Just inst -> inst.state == Active
    Nothing -> false

{-| Get the directory of the current instance. -}
getDirectory :: Aff (Maybe String)
getDirectory = do
  current <- getCurrentInstanceFFI
  pure $ map _.directory current

{-| Get the state of the current instance. -}
getState :: Aff (Maybe InstanceState)
getState = do
  current <- getCurrentInstanceFFI
  pure $ map _.state current
