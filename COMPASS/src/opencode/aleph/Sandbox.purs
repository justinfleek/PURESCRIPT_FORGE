{-|
Module      : Aleph.Sandbox
Description : Container isolation via gVisor
= Sandbox Isolation Layer

This module provides type-safe container isolation using gVisor (runsc).
All command execution requiring isolation MUST go through this layer.

== Module Structure

The Sandbox module is split into sub-modules for maintainability:

* "Aleph.Sandbox.Types" - Container config, mount types, exec output
* "Aleph.Sandbox.Policy" - Isolation policies and resource limits
* "Aleph.Sandbox.GVisor" - gVisor runtime management
* "Aleph.Sandbox.WASM" - WebAssembly sandboxing for untrusted code
* "Aleph.Sandbox.Proof" - Execution proofs and verification

== System F-w Encoding

@
  Kind Sandbox = Unrestricted | Network | Filesystem | GPU | Full

  -- Type constructor indexed by sandbox kind
  data Sandboxed :: Sandbox -> Type -> Type

  -- Functor over sandbox-indexed computations
  fmap :: forall (s :: Sandbox) a b. (a -> b) -> Sandboxed s a -> Sandboxed s b

  -- Escape hatch requires proof of sandbox completion
  runSandboxed :: forall (s :: Sandbox) a. SandboxProof s -> Sandboxed s a -> IO a
@

== Security Model

@
  +-----------------------------------------------------------+
  |                    Host Kernel                             |
  +-----------------------------------------------------------+
  |  +-----------+  +-----------+  +---------------------+    |
  |  |   runsc   |  |   Gofer   |  |       Sentry        |    |
  |  | (control) |  | (9P proxy)|  | (syscall intercept) |    |
  |  +-----------+  +-----+-----+  +----------+----------+    |
  |                       |                   |               |
  |                       v                   v               |
  |                 +-----------------------------+           |
  |                 |     Sandboxed Process       |           |
  |                 |     (user application)      |           |
  |                 +-----------------------------+           |
  +-----------------------------------------------------------+
@

== Coeffect Equation

@
  sandbox : ContainerConfig -> Graded Container (SandboxResult a)

  -- Requires:
  -- 1. Container resource for gVisor runtime
  -- 2. Filesystem for OCI bundle
@
-}
module Aleph.Sandbox
  ( -- * Re-exports
    module Aleph.Sandbox.Types
  , module Aleph.Sandbox.Policy
  , module Aleph.Sandbox.GVisor
  , module Aleph.Sandbox.WASM
  , module Aleph.Sandbox.Proof
    -- * Configuration Presets
  , defaultConfig
  , networkIsolated
  , filesystemIsolated
  , gpuEnabled
  , fullIsolation
  ) where

import Prelude

import Aleph.Sandbox.Types
import Aleph.Sandbox.Policy
import Aleph.Sandbox.GVisor
import Aleph.Sandbox.WASM
import Aleph.Sandbox.Proof

-- ============================================================================
-- CONFIGURATION PRESETS
-- ============================================================================

-- | Default secure configuration
defaultConfig :: ContainerConfig
defaultConfig =
  { image: "alpine:latest"
  , command: ["/bin/sh"]
  , workdir: "/workspace"
  , env: []
  , mounts: []
  , policy: policyFromKind RefFullIsolation
  , rootfs: ReadOnlyRootfs
  , networkMode: NoNetwork
  }

-- | Network isolated preset
networkIsolated :: ContainerConfig -> ContainerConfig
networkIsolated cfg = cfg
  { policy = policyFromKind RefNetworkOnly
  , networkMode = NoNetwork
  }

-- | Filesystem isolated preset
filesystemIsolated :: ContainerConfig -> ContainerConfig
filesystemIsolated cfg = cfg
  { policy = policyFromKind RefFilesystemOnly
  , mounts = []
  , rootfs = ReadOnlyRootfs
  }

-- | GPU enabled preset (for ML inference)
gpuEnabled :: ContainerConfig -> ContainerConfig
gpuEnabled cfg = cfg
  { policy = policyFromKind RefGPUPassthrough
  }

-- | Full isolation preset
fullIsolation :: ContainerConfig -> ContainerConfig
fullIsolation cfg = cfg
  { policy = policyFromKind RefFullIsolation
  , mounts = []
  , networkMode = NoNetwork
  , rootfs = ReadOnlyRootfs
  }
