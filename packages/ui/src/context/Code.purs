-- | Code Component Context
-- |
-- | Provides a context for the code display component.
-- | Allows parent components to inject their own code renderer.
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/context/code.tsx
module Forge.UI.Context.Code
  ( CodeComponentProvider
  , useCodeComponent
  , CodeComponentContext
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Halogen.HTML as HH

-- | The code component type (any valid component)
type CodeComponent = forall w i. HH.HTML w i

-- | Context for code component
type CodeComponentContext =
  { component :: CodeComponent
  }

-- | Internal context ref
foreign import codeContextRef :: Ref (Maybe CodeComponent)

-- | Provider component for code context
type CodeComponentProvider =
  { component :: CodeComponent
  , children :: Array (HH.HTML Unit Unit)
  } -> HH.HTML Unit Unit

-- | Use the code component from context
useCodeComponent :: Effect CodeComponent
useCodeComponent = do
  mComponent <- Ref.read codeContextRef
  case mComponent of
    Nothing -> throw "CodeComponent context must be used within a CodeComponentProvider"
    Just c -> pure c
