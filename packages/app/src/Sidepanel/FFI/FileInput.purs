-- | File Input FFI Module - File Selection and Reading
-- |
-- | **What:** Provides FFI bindings for file input elements, enabling file selection
-- |         and reading file contents from file picker, URLs, and File objects.
-- | **Why:** Enables import functionality by allowing users to select and read files.
-- | **How:** Uses browser FileReader API and Fetch API via FFI.
-- |
-- | 1:1 port from COMPASS Bridge.FFI.Node.FileContext (adapted for browser)
module Sidepanel.FFI.FileInput
  ( triggerFilePicker
  , fetchURLContent
  ) where

import Prelude
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Either (Either(..))
import Control.Promise (Promise, toAff)
import Effect (Effect)

-- | Trigger native file picker dialog and read selected file as text
-- | Returns the file content as a string, or fails with an error
triggerFilePicker :: Aff String
triggerFilePicker = toAff =<< liftEffect triggerFilePickerImpl

foreign import triggerFilePickerImpl :: Effect (Promise String)

-- | Fetch content from a URL as text
-- | Returns the response body as a string, or fails with HTTP error
fetchURLContent :: String -> Aff String
fetchURLContent url = toAff =<< liftEffect (fetchURLContentImpl url)

foreign import fetchURLContentImpl :: String -> Effect (Promise String)

-- Re-export liftEffect
import Effect.Class (liftEffect)
