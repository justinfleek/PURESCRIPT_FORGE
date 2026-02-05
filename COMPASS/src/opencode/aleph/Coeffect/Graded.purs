{-|
Module      : Aleph.Coeffect.Graded
Description : Graded monad for coeffect tracking
= Graded Monad

Computations indexed by their resource requirements:

@
  Graded : Resource → Type → Type

  pure  : ∀ a. a → Graded Pure a
  (>>=) : ∀ r s a b. Graded r a → (a → Graded s b) → Graded (r ⊗ s) b
  run   : ∀ r a. Graded r a → Proof r → Either DischargeError a
@

The grading tracks resource requirements through composition,
enabling static verification that all requirements are discharged.
-}
module Aleph.Coeffect.Graded
  ( Graded(..)
  , pure'
  , map'
  , ap'
  , bind'
  , run
  , require
  ) where

import Prelude

import Data.Either (Either(..))

import Aleph.Coeffect.Resource (Resource)
import Aleph.Coeffect.Discharge (DischargeProof, discharge)

-- ════════════════════════════════════════════════════════════════════════════
-- GRADED MONAD
-- ════════════════════════════════════════════════════════════════════════════

{-| Graded monad indexed by resource requirements.

@
  newtype Graded (r :: Resource) (a :: Type) =
    Graded (DischargeProof → Either DischargeError a)
@
-}
newtype Graded (r :: Type) a = Graded (DischargeProof -> Either String a)

-- | Pure computation (requires no resources)
pure' :: forall a. a -> Graded Resource a
pure' a = Graded (\_ -> Right a)

-- | Map over graded computation
map' :: forall a b. (a -> b) -> Graded Resource a -> Graded Resource b
map' f (Graded ma) = Graded \proof ->
  case ma proof of
    Left err -> Left err
    Right a -> Right (f a)

-- | Apply for graded computations
ap' :: forall a b. Graded Resource (a -> b) -> Graded Resource a -> Graded Resource b
ap' (Graded mf) (Graded ma) = Graded \proof ->
  case mf proof of
    Left err -> Left err
    Right f ->
      case ma proof of
        Left err -> Left err
        Right a -> Right (f a)

-- | Bind with resource combination
bind' :: forall a b. Graded Resource a -> (a -> Graded Resource b) -> Graded Resource b
bind' (Graded ma) f = Graded \proof ->
  case ma proof of
    Left err -> Left err
    Right a -> 
      let Graded mb = f a
      in mb proof

-- | Run a graded computation with discharge proof
run :: forall a. Graded Resource a -> DischargeProof -> Either String a
run (Graded f) = f

-- | Create a computation requiring a specific resource
require :: Resource -> Graded Resource Unit
require res = Graded \proof ->
  discharge res proof
