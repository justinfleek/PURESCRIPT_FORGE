/-
  Compass - Root module for COMPASS types

  This module re-exports all COMPASS types with their
  Extractable instances and roundtrip proofs.

  Usage:
    import Compass

  All types are extracted from proven Lean definitions.
-/

import Compass.Core
import Compass.Permissions
import Compass.Auth
import Compass.Tools
import Compass.Audit
import Compass.Jobs
import Compass.Emit

/-!
  # COMPASS Type System

  ## Core Types (with roundtrip proofs)

  ### Authentication
  - `Organization` - Multi-tenant organization
  - `User` - User identity with roles and permissions
  - `Session` - Web UI session
  - `APIKey` - Programmatic access key

  ### Permissions
  - `Permission` - Fine-grained permission enum (21 variants)
  - `Role` - User role enum (ADMIN, MANAGER, CREATOR, VIEWER)

  ### Tools
  - `RateLimit` - Rate limiting configuration
  - `ToolResult` - Result from tool execution
  - `CallContext` - Request context for tracing

  ### Audit
  - `TransformationType` - Data transformation enum
  - `AuditRecord` - Immutable audit log entry
  - `ProvenanceNode` - Data lineage tracking

  ### Jobs
  - `JobStatus` - Job state enum
  - `Job` - Unit of work with approval workflow

  ## Invariants (Theorems)

  Each type has associated invariants that must hold:
  - `User.passwordHashValid` - Password hash must be non-empty if present
  - `Session.expiryValid` - Expiry must be after creation
  - `APIKey.prefixValid` - Key prefix must be 8 chars starting with "flk_"
  - `AuditRecord.chainValid` - Hash chain integrity
  - `Job.completedHasTimestamp` - Completed jobs have completion time
  - `Job.failedHasError` - Failed jobs have error message

  ## Code Generation

  Use `lake exe extract` to generate:
  - `elm` - Elm types with decoders/encoders
  - `python` - Python dataclasses with enums

  Every generated type has a proven `decode(encode(x)) = x` theorem.
-/
