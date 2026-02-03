-- | Function utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/fn.ts
module Forge.Util.Fn where

import Prelude

-- | Identity function
identity :: forall a. a -> a
identity x = x

-- | Constant function
constant :: forall a b. a -> b -> a
constant x _ = x

-- | Compose two functions
compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

-- | Pipe a value through functions
pipe :: forall a b. a -> (a -> b) -> b
pipe x f = f x
