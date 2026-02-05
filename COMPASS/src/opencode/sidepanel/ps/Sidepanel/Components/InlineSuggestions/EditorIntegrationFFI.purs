{-|
Module      : Sidepanel.Components.InlineSuggestions.EditorIntegrationFFI
Description : FFI for editor integration

FFI declarations for integrating with actual editor (Monaco, CodeMirror, etc.).
-}
module Sidepanel.Components.InlineSuggestions.EditorIntegrationFFI where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( EditorState
  , Position
  , Range
  )

-- | Get current editor state
foreign import getCurrentEditorStateFFI :: Effect EditorState

-- | Get cursor position from editor
foreign import getCursorPositionFFI :: Effect Position

-- | Insert text at cursor position
foreign import insertTextAtCursorFFI :: String -> Effect Boolean

-- | Replace text in range
foreign import replaceTextInRangeFFI :: Range -> String -> Effect Boolean

-- | Calculate pixel position from line/column
foreign import calculatePixelPositionFFI :: Position -> Effect { top :: Number, left :: Number }

-- | Register editor change listener
foreign import registerEditorChangeListenerFFI :: (EditorChangeEvent -> Effect Unit) -> Effect (Effect Unit)

-- | Editor change event (matches EditorIntegration.purs)
type EditorChangeEvent =
  { filePath :: String
  , content :: String
  , cursorPosition :: Position
  , changeType :: String  -- "insertion" | "deletion" | "cursorMove" | "fileOpen" | "fileSave"
  , timestamp :: Number
  }

-- | Get editor container element (for positioning overlay)
foreign import getEditorContainerFFI :: Effect (Effect.Element)

-- | Import Effect.Element
import Effect (Element) as Effect
