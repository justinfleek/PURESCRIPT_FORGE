-- | Stripe Webhook Route Handler
-- | Main entry point for Stripe webhook requests
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/stripe/webhook.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Stripe.Webhook
  ( handleWebhookPOST
  ) where

import Prelude

import Effect.Aff (Aff)
import Console.App.FFI.SolidStart (APIEvent, Response)
import Console.App.Routes.Stripe.Webhook.Main (handleWebhookPOST)

-- | Re-export main handler
-- | This module serves as the public API for the Stripe webhook route
