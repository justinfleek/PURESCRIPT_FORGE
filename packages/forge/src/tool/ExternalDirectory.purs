-- | External directory access validation
-- | FFI bindings to _archive/legacy/opencode-original/opencode-dev/packages/opencode/src/tool/external-directory.ts
module Forge.Tool.ExternalDirectory
  ( assertExternalDirectory
  , AssertOptions
  , ToolContext
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | Options for external directory assertion
type AssertOptions =
  { bypass :: Maybe Boolean
  , kind :: Maybe String  -- "file" | "directory"
  }

-- | Tool context type
type ToolContext =
  { ask :: Foreign -> Aff Unit
  }

-- | Assert that access to external directory is permitted
-- | If target is within project, no permission needed
-- | Otherwise, prompts user for permission
foreign import assertExternalDirectory :: ToolContext -> Maybe String -> Maybe AssertOptions -> Aff Unit
