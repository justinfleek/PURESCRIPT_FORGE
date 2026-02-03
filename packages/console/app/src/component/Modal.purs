-- | Modal Component
-- |
-- | Modal dialog overlay.
-- | Pure data representation of modal state.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/component/modal.tsx
module Forge.Console.App.Component.Modal
  ( ModalProps
  , ModalState
  , ModalAction(..)
  , initialState
  , reduce
  , isVisible
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Modal component props
type ModalProps =
  { open :: Boolean
  , title :: Maybe String
  }

-- | Modal component state
type ModalState =
  { isOpen :: Boolean
  }

-- | Modal actions
data ModalAction
  = Open
  | Close
  | ClickOverlay
  | ClickContent  -- Stops propagation

derive instance eqModalAction :: Eq ModalAction

-- | Initial modal state
initialState :: ModalState
initialState = { isOpen: false }

-- | Reduce modal actions
reduce :: ModalAction -> ModalState -> ModalState
reduce action state = case action of
  Open -> state { isOpen = true }
  Close -> state { isOpen = false }
  ClickOverlay -> state { isOpen = false }
  ClickContent -> state  -- No change, stops event propagation

-- | Check if modal is visible
isVisible :: ModalProps -> Boolean
isVisible props = props.open
