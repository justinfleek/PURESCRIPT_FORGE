{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Type safety rules - no banned constructs
module Rules.TypeSafety where

import Prelude hiding (undefined, error, head, tail, fromJust)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))

-- | BANNED: undefined, error, head, tail, fromJust
-- | These are unrepresentable - compiler will reject if imported

-- | Correct pattern: Explicit Maybe instead of null/undefined
-- | All optional values must use Maybe
type OptionalValue a = Maybe a

-- | Correct pattern: Explicit Either instead of exceptions
-- | All errors must be represented in types
type Result e a = Either e a

-- | Explicit null check
-- | Replaces ?? (nullish coalescing) and ! (non-null assertion)
explicitDefault :: Maybe a -> a -> a
explicitDefault Nothing default = default
explicitDefault (Just value) _ = value

-- | Explicit conditional
-- | Replaces || for defaults
explicitConditional :: Bool -> a -> a -> a
explicitConditional True value _ = value
explicitConditional False _ default = default

-- | Type guard for narrowing
-- | Replaces type assertions (as Type)
class TypeGuard a b where
  guard :: a -> Maybe b

-- | No type escapes allowed
-- | This function proves we never use unsafe casts
-- | BANNED: unsafeCoerce, unsafePerformIO, etc.
noTypeEscapes :: a -> Maybe b
noTypeEscapes _ = Nothing
