-- | Context Helper - Simple Context Creation Pattern
-- |
-- | PureScript implementation of the createSimpleContext pattern.
-- | Provides a type-safe way to create React-like contexts with
-- | automatic provider/consumer pairing.
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/context/helper.tsx
module Forge.UI.Context.Helper
  ( SimpleContext
  , SimpleContextConfig
  , createSimpleContext
  , useContext
  , ContextProvider
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- | Configuration for creating a simple context
type SimpleContextConfig props value =
  { name :: String
  , init :: props -> value
  , gate :: Maybe Boolean
  }

-- | A simple context with provider and use functions
type SimpleContext props value =
  { provider :: ContextProvider props value
  , use :: Effect value
  }

-- | Context provider component type
type ContextProvider props value =
  { props :: props
  , children :: Array (HH.HTML Unit Unit)
  } -> HH.HTML Unit Unit

-- | Internal context storage
foreign import data ContextStore :: Type -> Type

-- | Create a context store
foreign import createContextStore :: forall a. Effect (Ref (Maybe a))

-- | Create a simple context with provider and consumer
createSimpleContext 
  :: forall props value
   . SimpleContextConfig props value 
  -> Effect (SimpleContext props value)
createSimpleContext config = do
  storeRef <- Ref.new Nothing
  
  let
    provider :: ContextProvider props value
    provider { props, children } =
      let value = config.init props
      in HH.div 
           [ HP.attr (HH.AttrName "data-context") config.name ]
           children
    
    use :: Effect value
    use = do
      mValue <- Ref.read storeRef
      case mValue of
        Nothing -> throw $ config.name <> " context must be used within a provider"
        Just v -> pure v

  pure { provider, use }

-- | Use a context value (throws if not in provider)
useContext :: forall value. Ref (Maybe value) -> String -> Effect value
useContext ref name = do
  mValue <- Ref.read ref
  case mValue of
    Nothing -> throw $ name <> " context must be used within a context provider"
    Just v -> pure v
