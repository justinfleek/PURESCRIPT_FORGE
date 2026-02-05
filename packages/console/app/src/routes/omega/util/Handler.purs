-- | Omega Handler - Main Request Processing
-- |
-- | Main entry point for Omega API request handling.
-- | Delegates to Handler.Main for orchestration.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/handler.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Handler
  ( HandlerOptions
  , handleOmegaRequest
  ) where

import Prelude

import Effect.Aff (Aff)
import Console.App.FFI.SolidStart (APIEvent, Response)
import Console.App.Routes.Omega.Util.Handler.Main (handleOmegaRequest, HandlerOptions)
