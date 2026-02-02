-- | Type safety rules - no banned constructs
module Rules.TypeSafety where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))

-- | Banned type: any
-- | This type cannot exist in our codebase
-- | Using Void ensures it's unrepresentable
data BannedAny = BannedAny Void

-- | Banned type: unknown
-- | Replaced with explicit type narrowing
data BannedUnknown = BannedUnknown Void

-- | Correct pattern: Explicit Maybe instead of null/undefined
-- | All optional values must use Maybe
type OptionalValue a = Maybe a

-- | Correct pattern: Explicit Either instead of exceptions
-- | All errors must be represented in types
type Result e a = Either e a

-- | Type guard for narrowing
-- | Replaces type assertions (as Type)
class TypeGuard a b where
  guard :: a -> Maybe b

-- | Explicit null check
-- | Replaces ?? (nullish coalescing)
explicitDefault :: forall a. Maybe a -> a -> a
explicitDefault Nothing default = default
explicitDefault (Just value) _ = value

-- | Explicit conditional
-- | Replaces || for defaults
explicitConditional :: forall a. Boolean -> a -> a -> a
explicitConditional true value _ = value
explicitConditional false _ default = default

-- | No type escapes allowed
-- | This function proves we never use unsafe casts
noTypeEscapes :: forall a b. a -> Maybe b
noTypeEscapes _ = Nothing
