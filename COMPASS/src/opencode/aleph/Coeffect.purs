{-|
Module      : Aleph.Coeffect
Description : Re-exports for coeffect system
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Aleph Coeffect System

Coeffects describe what a computation REQUIRES from its environment.

== Module Structure

@
  Aleph.Coeffect
  ├── Spec       -- Resource specifications (SandboxKind, PathSpec, etc.)
  ├── Resource   -- Resource algebra (combine, flatten, requires)
  ├── Graded     -- Graded monad (pure', bind', run)
  └── Discharge  -- Discharge proofs (NetworkAccess, AuthProof, etc.)
@

== Quick Reference

@
  -- Create resources
  network              : Resource
  auth "github"        : Resource
  filesystem pathSpec  : Resource
  container spec       : Resource

  -- Combine resources
  network ⊗ auth "hf"  : Resource

  -- Graded computations
  pure' x              : Graded Pure a
  m `bind'` f          : Graded (r ⊗ s) b

  -- Run with proof
  run computation proof : Either Error a
@
-}
module Aleph.Coeffect
  ( module Aleph.Coeffect.Spec
  , module Aleph.Coeffect.Resource
  , module Aleph.Coeffect.Graded
  , module Aleph.Coeffect.Discharge
  , module Aleph.Coeffect.Constructors
  ) where

import Aleph.Coeffect.Spec
import Aleph.Coeffect.Resource
import Aleph.Coeffect.Graded
import Aleph.Coeffect.Discharge
import Aleph.Coeffect.Constructors
