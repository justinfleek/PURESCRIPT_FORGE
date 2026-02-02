-- | Main Entry Point - Application Bootstrap
-- |
-- | **What:** The main entry point for the OpenCode Sidepanel application. Bootstraps the
-- |         Halogen application and mounts it to the DOM.
-- | **Why:** Provides the entry point for the PureScript application, initializes Halogen
-- |         runtime, and connects the application to the DOM.
-- | **How:** Uses Halogen.Aff to run the Halogen application in an Aff context, awaits
-- |         the DOM body element, and mounts the App component using runUI.
-- |
-- | **Dependencies:**
-- | - `Halogen.Aff`: Halogen Aff runtime
-- | - `Halogen.VDom.Driver`: Virtual DOM driver for rendering
-- | - `Sidepanel.App`: Root application component
-- |
-- | **Usage Example:**
-- | ```purescript
-- | -- In HTML/JavaScript:
-- | import { main } from "./output/Sidepanel.Main/index.js"
-- | main()
-- |
-- | -- Or via bundler entry point:
-- | // index.js
-- | import { main } from "./output/Sidepanel.Main/index.js"
-- | main()
-- | ```
-- |
-- | Based on spec 40-PURESCRIPT-ARCHITECTURE.md
module Sidepanel.Main where

import Prelude
import Effect (Effect)
import Halogen.Aff as HA
import Halogen.VDom.Driver (runUI)
import Sidepanel.App as App

main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  runUI App.component unit body
