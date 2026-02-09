-- | Storage - file-based JSON storage
-- | 1:1 parity with opencode-dev/packages/opencode/src/storage/storage.ts
module Forge.Storage.Storage
  ( -- * Types
    StorageKey
  , NotFoundError
    -- * Operations
  , read
  , write
  , update
  , remove
  , list
  , exists
  ) where

import Prelude
import Effect.Aff (Aff)
import Foreign (Foreign)

-- | Storage key path (array of strings representing nested keys)
type StorageKey = Array String

-- | NotFoundError type for error handling
foreign import data NotFoundError :: Type

-- ============================================================================
-- FFI IMPORTS
-- ============================================================================

-- | Read value from storage
foreign import read :: StorageKey -> Aff Foreign

-- | Write value to storage
foreign import write :: StorageKey -> Foreign -> Aff Unit

-- | Update value in storage with a modifier function
foreign import update :: StorageKey -> (Foreign -> Foreign) -> Aff Foreign

-- | Remove value from storage
foreign import remove :: StorageKey -> Aff Unit

-- | List all keys under a prefix
foreign import list :: StorageKey -> Aff (Array StorageKey)

-- | Check if key exists
foreign import exists :: StorageKey -> Aff Boolean
