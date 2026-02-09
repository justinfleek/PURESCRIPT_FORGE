-- | Compatibility shim for the deprecated purescript-math package
-- | Re-exports standard math functions under the Math module name
module Math
  ( pow
  , min
  , max
  , floor
  ) where

import Data.Ord as Ord

-- | Minimum of two numbers
min :: Number -> Number -> Number
min = Ord.min

-- | Maximum of two numbers
max :: Number -> Number -> Number
max = Ord.max

-- | Raise a number to a power
foreign import pow :: Number -> Number -> Number

-- | Floor of a number
foreign import floor :: Number -> Number
