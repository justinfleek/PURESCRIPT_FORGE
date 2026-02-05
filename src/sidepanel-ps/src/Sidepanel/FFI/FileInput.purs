-- | File Input FFI Module - File Selection and Reading
-- |
-- | **What:** Provides FFI bindings for file input elements, enabling file selection
-- |         and reading file contents.
-- | **Why:** Enables import functionality by allowing users to select and read files.
-- | **How:** Uses foreign function imports to handle file input events and read file contents.
module Sidepanel.FFI.FileInput where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, makeAff)
import Data.Either (Either)

-- | Read file content as text
foreign import readFileAsText :: String -> Aff (Either String String)

-- | Create file input element and trigger file picker
foreign import triggerFilePicker :: Effect Unit
