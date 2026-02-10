-- | Haskell Database FFI - Forward Declaration
-- | Full implementation in bridge/ batch (Batch 7)
module Bridge.FFI.Haskell.Database where

-- | Opaque Database handle
foreign import data Database :: Type
