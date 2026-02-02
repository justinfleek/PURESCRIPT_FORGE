{-|
Module      : Aleph.Sandbox.Policy
Description : Sandbox policies and isolation levels
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Sandbox Policy

This module defines sandbox policies that control resource access
and isolation levels for containerized execution.

== Policy Derivation

Policies are derived from sandbox kinds:

| Kind           | Network | Filesystem | GPU   | Memory | CPU  |
|----------------|---------|------------|-------|--------|------|
| Unrestricted   | Yes     | Yes        | Yes   | None   | 100% |
| NetworkOnly    | No      | Yes        | No    | 4GB    | 80%  |
| FilesystemOnly | Yes     | No         | No    | 2GB    | 50%  |
| GPUPassthrough | No      | No         | Yes   | 16GB   | 100% |
| FullIsolation  | No      | No         | No    | 1GB    | 25%  |

== Coeffect Integration

Policies map to coeffect requirements:
@
  policyToCoeffect : SandboxPolicy -> Resource
  policyToCoeffect p = 
    (if p.allowNetwork then Network else Unit) *
    (if p.allowFilesystem then Filesystem [] else Unit) *
    (if p.allowGPU then GPU else Unit)
@
-}
module Aleph.Sandbox.Policy
  ( -- * Policy Type
    SandboxPolicy(..)
    -- * Policy Derivation
  , policyFromKind
    -- * Isolation Level
  , IsolationLevel(..)
  , deriveIsolationLevel
    -- * Resource Usage
  , ResourceUsage(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ============================================================================
-- SANDBOX POLICY
-- ============================================================================

{-| Policy for sandbox behavior.

@
  record SandboxPolicy where
    constructor MkPolicy
    allowNetwork    : Bool
    allowFilesystem : Bool
    allowGPU        : Bool
    allowIPC        : Bool
    maxMemoryMB     : Nat
    maxCPUPercent   : Nat
    timeoutMs       : Nat
@
-}
type SandboxPolicy =
  { allowNetwork :: Boolean
  , allowFilesystem :: Boolean
  , allowGPU :: Boolean
  , allowIPC :: Boolean
  , maxMemoryMB :: Int
  , maxCPUPercent :: Int
  , timeoutMs :: Int
  }

-- | Sandbox kind for policy derivation (forward declaration pattern)
data SandboxKindRef
  = RefUnrestricted
  | RefNetworkOnly
  | RefFilesystemOnly
  | RefGPUPassthrough
  | RefFullIsolation

-- | Derive policy from kind
policyFromKind :: SandboxKindRef -> SandboxPolicy
policyFromKind = case _ of
  RefUnrestricted ->
    { allowNetwork: true
    , allowFilesystem: true
    , allowGPU: true
    , allowIPC: true
    , maxMemoryMB: 0       -- 0 = unlimited
    , maxCPUPercent: 100
    , timeoutMs: 0         -- 0 = no timeout
    }
  RefNetworkOnly ->
    { allowNetwork: false
    , allowFilesystem: true
    , allowGPU: false
    , allowIPC: false
    , maxMemoryMB: 4096
    , maxCPUPercent: 80
    , timeoutMs: 300000    -- 5 minutes
    }
  RefFilesystemOnly ->
    { allowNetwork: true
    , allowFilesystem: false
    , allowGPU: false
    , allowIPC: false
    , maxMemoryMB: 2048
    , maxCPUPercent: 50
    , timeoutMs: 120000    -- 2 minutes
    }
  RefGPUPassthrough ->
    { allowNetwork: false
    , allowFilesystem: false
    , allowGPU: true
    , allowIPC: false
    , maxMemoryMB: 16384
    , maxCPUPercent: 100
    , timeoutMs: 600000    -- 10 minutes
    }
  RefFullIsolation ->
    { allowNetwork: false
    , allowFilesystem: false
    , allowGPU: false
    , allowIPC: false
    , maxMemoryMB: 1024
    , maxCPUPercent: 25
    , timeoutMs: 60000     -- 1 minute
    }

-- ============================================================================
-- ISOLATION LEVEL
-- ============================================================================

data IsolationLevel
  = IsoNone
  | IsoPartial
  | IsoFull

derive instance eqIsolationLevel :: Eq IsolationLevel
derive instance ordIsolationLevel :: Ord IsolationLevel
derive instance genericIsolationLevel :: Generic IsolationLevel _

instance showIsolationLevel :: Show IsolationLevel where
  show = genericShow

-- | Derive isolation level from policy
deriveIsolationLevel :: SandboxPolicy -> IsolationLevel
deriveIsolationLevel policy
  | policy.allowNetwork && policy.allowFilesystem && policy.allowGPU = IsoNone
  | not policy.allowNetwork && not policy.allowFilesystem = IsoFull
  | otherwise = IsoPartial

-- ============================================================================
-- RESOURCE USAGE
-- ============================================================================

type ResourceUsage =
  { cpuMs :: Int
  , memoryMB :: Int
  , diskMB :: Int
  , networkBytes :: Int
  }
