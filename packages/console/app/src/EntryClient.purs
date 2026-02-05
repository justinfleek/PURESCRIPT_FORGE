-- | Client Entry Point
-- |
-- | Mounts SolidJS Start client application to the DOM.
-- | PureScript wrapper around SolidJS Start's mount function.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/entry-client.tsx
-- | Migrated: 2026-02-04
module Console.App.EntryClient
  ( mountClient
  ) where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)

-- | FFI: Mount SolidJS Start client
-- | Calls: mount(() => <StartClient />, document.getElementById("app")!)
foreign import mountClient :: Effect Unit
