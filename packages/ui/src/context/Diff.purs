-- | Diff Component Context
-- |
-- | Provides a context for the diff display component.
-- | Allows parent components to inject their own diff renderer.
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/context/diff.tsx
module Forge.UI.Context.Diff
  ( DiffComponentProvider
  , useDiffComponent
  , DiffComponentContext
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Halogen.HTML as HH

-- | The diff component type (any valid component)
type DiffComponent = forall w i. HH.HTML w i

-- | Context for diff component
type DiffComponentContext =
  { component :: DiffComponent
  }

-- | Internal context ref
foreign import diffContextRef :: Ref (Maybe DiffComponent)

-- | Provider component for diff context
type DiffComponentProvider =
  { component :: DiffComponent
  , children :: Array (HH.HTML Unit Unit)
  } -> HH.HTML Unit Unit

-- | Use the diff component from context
useDiffComponent :: Effect DiffComponent
useDiffComponent = do
  mComponent <- Ref.read diffContextRef
  case mComponent of
    Nothing -> throw "DiffComponent context must be used within a DiffComponentProvider"
    Just c -> pure c
