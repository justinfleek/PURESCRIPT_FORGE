{-|
Module      : Aleph.Coeffect.Resource
Description : Resource algebra for coeffect tracking
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Resource Algebra

Resources form a semilattice under combination (⊗):

@
  -- Semilattice laws:
  Pure ⊗ r = r                    -- left identity
  r ⊗ Pure = r                    -- right identity  
  r ⊗ (s ⊗ t) = (r ⊗ s) ⊗ t      -- associativity
  r ⊗ s = s ⊗ r                   -- commutativity
  r ⊗ r = r                       -- idempotence
@

Each resource represents an external requirement that must be
discharged before computation can proceed.
-}
module Aleph.Coeffect.Resource
  ( Resource(..)
  , combine
  , (⊗)
  , flatten
  , requires
  , subsumes
  , ResourceSet
  , emptySet
  , singleton
  , union
  , member
  , toList
  ) where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Set as Set
import Data.Argonaut (class EncodeJson, encodeJson)

import Aleph.Coeffect.Spec 
  ( SandboxKind
  , ContainerSpec
  , PathSpec
  , GPUSpec
  , SearchBackend
  , ASTLanguage
  )

-- ════════════════════════════════════════════════════════════════════════════
-- RESOURCE TYPE
-- ════════════════════════════════════════════════════════════════════════════

{-| Resource algebra - what a computation requires.

@
  data Resource :: Type where
    Pure       : Resource
    Network    : Resource
    Auth       : String → Resource
    Sandbox    : SandboxKind → Resource
    Container  : ContainerSpec → Resource
    Filesystem : PathSpec → Resource
    GPU        : GPUSpec → Resource
    Search     : SearchBackend → Resource
    AST        : ASTLanguage → Resource
    Both       : Resource → Resource → Resource
@
-}
data Resource
  = Pure                           -- Needs nothing external
  | Network                        -- Needs network access
  | Auth String                    -- Needs credential for provider
  | Sandbox SandboxKind            -- Needs isolation
  | Container ContainerSpec        -- Needs gVisor container
  | Filesystem PathSpec            -- Needs filesystem access
  | GPU GPUSpec                    -- Needs GPU compute
  | Search SearchBackend           -- Needs search engine
  | AST ASTLanguage                -- Needs AST parser
  | Both Resource Resource         -- Composition of resources

derive instance eqResource :: Eq Resource
derive instance ordResource :: Ord Resource
derive instance genericResource :: Generic Resource _

instance showResource :: Show Resource where
  show = genericShow

instance encodeJsonResource :: EncodeJson Resource where
  encodeJson = case _ of
    Pure -> encodeJson { tag: "pure" }
    Network -> encodeJson { tag: "network" }
    Auth name -> encodeJson { tag: "auth", provider: name }
    Sandbox kind -> encodeJson { tag: "sandbox", kind: show kind }
    Container spec -> encodeJson { tag: "container", image: spec.image }
    Filesystem spec -> encodeJson { tag: "filesystem", path: spec.path }
    GPU spec -> encodeJson { tag: "gpu", device: spec.deviceIndex }
    Search backend -> encodeJson { tag: "search", backend: show backend }
    AST lang -> encodeJson { tag: "ast", language: show lang }
    Both r1 r2 -> encodeJson 
      { tag: "both"
      , left: encodeJson r1
      , right: encodeJson r2 
      }

-- ════════════════════════════════════════════════════════════════════════════
-- SEMILATTICE OPERATIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Combine two resources (tensor product)
combine :: Resource -> Resource -> Resource
combine Pure r = r
combine r Pure = r
combine r1 r2 = Both r1 r2

-- | Infix operator for resource combination
infixr 7 combine as ⊗

-- | Flatten a resource tree into atomic resources
flatten :: Resource -> Array Resource
flatten = case _ of
  Pure -> []
  Both r1 r2 -> flatten r1 <> flatten r2
  r -> [r]

-- | Check if r1 requires r2 (r2 is subset of r1)
requires :: Resource -> Resource -> Boolean
requires r1 r2 = 
  let set1 = Set.fromFoldable (flatten r1)
      set2 = Set.fromFoldable (flatten r2)
  in Set.subset set2 set1

-- | Check if r1 subsumes r2
subsumes :: Resource -> Resource -> Boolean
subsumes = requires

-- ═══��════════════════════════════════════════════════════════════════════════
-- RESOURCE SETS
-- ════════════════════════════════════════════════════════════════════════════

type ResourceSet = Set.Set Resource

emptySet :: ResourceSet
emptySet = Set.empty

singleton :: Resource -> ResourceSet
singleton = Set.singleton

union :: ResourceSet -> ResourceSet -> ResourceSet
union = Set.union

member :: Resource -> ResourceSet -> Boolean
member = Set.member

toList :: ResourceSet -> Array Resource
toList = Set.toUnfoldable
