-- | Download FFI Module - File Download Functionality
-- |
-- | **What:** Provides FFI bindings for triggering file downloads in the browser, allowing
-- |         users to save content (e.g., session exports, snapshots) as files.
-- | **Why:** Enables users to export data from the sidepanel (sessions, snapshots) for
-- |         backup, sharing, or analysis. Essential for data portability.
-- | **How:** Uses foreign function imports to create download links and trigger browser
-- |         download dialog. Typically creates a blob URL and triggers click on anchor element.
-- |
-- | **Dependencies:** None (pure FFI bindings)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.FFI.Download as Download
-- |
-- | -- Download file
-- | liftEffect $ Download.downloadFile "file content" "filename.json"
-- | ```
module Sidepanel.FFI.Download where

import Prelude
import Effect (Effect)

-- | Download file with content and filename
foreign import downloadFile :: String -> String -> Effect Unit
