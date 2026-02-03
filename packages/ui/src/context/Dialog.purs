-- | Dialog Context - Modal Dialog Management
-- |
-- | Provides a context for managing modal dialogs with proper
-- | lifecycle, escape key handling, and overlay management.
-- |
-- | Source: _OTHER/opencode-original/packages/ui/src/context/dialog.tsx
module Forge.UI.Context.Dialog
  ( DialogContext
  , DialogProvider
  , useDialog
  , DialogElement
  , ActiveDialog
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Halogen.HTML as HH

-- | A dialog element is a function that returns HTML
type DialogElement = Unit -> HH.HTML Unit Unit

-- | Active dialog state
type ActiveDialog =
  { id :: String
  , node :: HH.HTML Unit Unit
  , dispose :: Effect Unit
  , onClose :: Maybe (Effect Unit)
  , setClosing :: Boolean -> Effect Unit
  }

-- | Dialog context interface
type DialogContext =
  { active :: Maybe ActiveDialog
  , show :: DialogElement -> Maybe (Effect Unit) -> Effect Unit
  , close :: Effect Unit
  }

-- | Internal context reference
foreign import dialogContextRef :: Ref (Maybe DialogContext)

-- | Dialog provider component
type DialogProvider = 
  { children :: Array (HH.HTML Unit Unit) 
  } -> HH.HTML Unit Unit

-- | Initialize dialog context
initDialogContext :: Effect DialogContext
initDialogContext = do
  activeRef <- Ref.new Nothing
  lockRef <- Ref.new false
  
  let
    close :: Effect Unit
    close = do
      mActive <- Ref.read activeRef
      locked <- Ref.read lockRef
      case mActive of
        Nothing -> pure unit
        Just active | locked -> pure unit
        Just active -> do
          Ref.write true lockRef
          -- Call onClose callback if present
          case active.onClose of
            Nothing -> pure unit
            Just onClose -> onClose
          -- Set closing state
          active.setClosing true
          -- Dispose after animation delay
          active.dispose
          Ref.write Nothing activeRef
          Ref.write false lockRef

    show :: DialogElement -> Maybe (Effect Unit) -> Effect Unit
    show element onClose = do
      -- Dispose existing dialog
      mCurrent <- Ref.read activeRef
      case mCurrent of
        Just current -> current.dispose
        Nothing -> pure unit
      
      Ref.write false lockRef
      
      -- Generate unique ID
      id <- generateId
      
      -- Create new dialog state
      closingRef <- Ref.new false
      let
        newDialog =
          { id
          , node: element unit
          , dispose: Ref.write Nothing activeRef
          , onClose
          , setClosing: \c -> Ref.write c closingRef
          }
      
      Ref.write (Just newDialog) activeRef

  pure { active: Nothing, show, close }

-- | Generate a random ID
foreign import generateId :: Effect String

-- | Use the dialog context
useDialog :: Effect DialogContext
useDialog = do
  mCtx <- Ref.read dialogContextRef
  case mCtx of
    Nothing -> throw "useDialog must be used within a DialogProvider"
    Just ctx -> pure ctx
