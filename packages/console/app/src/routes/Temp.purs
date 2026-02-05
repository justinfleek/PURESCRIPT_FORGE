-- | Temp Route (Home Page)
-- | Home page with copy-to-clipboard functionality
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/temp.tsx
-- | Migrated: 2026-02-04
module Console.App.Routes.Temp
  ( page
  ) where

import Prelude

import Effect.Aff (Aff)
import Console.App.FFI.SolidStart (PageProps, Response)

-- | Page handler (FFI boundary - SolidJS Start route)
-- | Returns HTML response with copy-to-clipboard functionality
page :: PageProps -> Aff Response
page _props = renderTempPage

foreign import renderTempPage :: Aff Response
