{-|
Module      : Forge.Aleph.Coeffect
Description : Re-exports for coeffect system
= Aleph Coeffect System

Coeffects describe what a computation REQUIRES from its environment.

== Module Structure

@
  Forge.Aleph.Coeffect
  +-- Spec       -- Resource specifications (SandboxKind, PathSpec, etc.)
  +-- Resource   -- Resource algebra (combine, flatten, requires)
  +-- Graded     -- Graded monad (pure', bind', run)
  +-- Discharge  -- Discharge proofs (NetworkAccess, AuthProof, etc.)
@

== Quick Reference

@
  -- Create resources
  network              : Resource
  auth "github"        : Resource
  filesystem pathSpec  : Resource
  container spec       : Resource

  -- Combine resources
  network `combine` auth "hf"  : Resource

  -- Graded computations
  pure' x              : Graded Pure a
  m `bind'` f          : Graded (r tensor s) b

  -- Run with proof
  run computation proof : Either Error a
@
-}
module Forge.Aleph.Coeffect
  ( module Forge.Aleph.Coeffect.Spec
  , module Forge.Aleph.Coeffect.Resource
  , module Forge.Aleph.Coeffect.Graded
  , module Forge.Aleph.Coeffect.Discharge
  , module Forge.Aleph.Coeffect.Constructors
  ) where

import Forge.Aleph.Coeffect.Spec
import Forge.Aleph.Coeffect.Resource
import Forge.Aleph.Coeffect.Graded
import Forge.Aleph.Coeffect.Discharge
import Forge.Aleph.Coeffect.Constructors
