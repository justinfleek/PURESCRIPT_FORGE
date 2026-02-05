{-|
Module      : Aleph.Coeffect.Constructors
Description : Smart constructors for resources
= Resource Constructors

Convenience functions for creating resources:

@
  network              -- Network access
  auth "github"        -- Auth for provider
  filesystem pathSpec  -- Filesystem access
  container spec       -- gVisor container
  gpu gpuSpec          -- GPU compute
  searchRes backend    -- Search engine
  astRes language      -- AST parser
@
-}
module Aleph.Coeffect.Constructors
  ( network
  , auth
  , sandbox
  , container
  , filesystem
  , gpu
  , searchRes
  , astRes
  ) where

import Aleph.Coeffect.Spec 
  ( SandboxKind
  , ContainerSpec
  , PathSpec
  , GPUSpec
  , SearchBackend
  , ASTLanguage
  )
import Aleph.Coeffect.Resource (Resource(..))

-- | Network access coeffect
network :: Resource
network = Network

-- | Authentication coeffect for a provider
auth :: String -> Resource
auth = Auth

-- | Sandbox isolation coeffect
sandbox :: SandboxKind -> Resource
sandbox = Sandbox

-- | gVisor container coeffect
container :: ContainerSpec -> Resource
container = Container

-- | Filesystem access coeffect
filesystem :: PathSpec -> Resource
filesystem = Filesystem

-- | GPU compute coeffect
gpu :: GPUSpec -> Resource
gpu = GPU

-- | Search engine coeffect
searchRes :: SearchBackend -> Resource
searchRes = Search

-- | AST parser coeffect
astRes :: ASTLanguage -> Resource
astRes = AST
