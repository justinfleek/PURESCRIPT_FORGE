-- | File Context View Component - AI Context Window Visibility
-- |
-- | **What:** Displays files currently in the AI context window, organized by directory.
-- |         Shows token usage per file, context budget, and provides management tools.
-- | **Why:** Enables users to understand what files are being sent to the AI, manage
-- |         context window size, and optimize token usage.
-- | **How:** Groups files by directory, displays token counts and budget usage, provides
-- |         filtering and search, and allows adding/removing files.
-- |
-- | Coeffect Equation:
-- |   FileContextView : Input -> Component q Input Output m
-- |   with tracking: Files^n -o Budget -> View
-- |
-- | Module Structure:
-- |   FileContextView.Types   - Type definitions
-- |   FileContextView.Render  - Rendering functions
-- |   FileContextView.Handler - Action handling
-- |
-- | Spec 58: AI Context Visibility
module Sidepanel.Components.FileContextView
  ( -- * Component
    component
    -- * Re-exports from Types
  , module Sidepanel.Components.FileContextView.Types
  ) where

import Prelude
import Halogen as H
import Effect.Aff.Class (class MonadAff)
import Data.Maybe (Maybe(..))

-- Re-export types
import Sidepanel.Components.FileContextView.Types
  ( FileInContext
  , FileStatus(..)
  , DirectoryGroup
  , ContextBudget
  , State
  , Action(..)
  , Output(..)
  , Input
  , initialState
  , groupFilesByDirectory
  , calculateBudget
  , detectLanguage
  )

-- Internal imports
import Sidepanel.Components.FileContextView.Render (render)
import Sidepanel.Components.FileContextView.Handler (handleAction)

--------------------------------------------------------------------------------
-- | Component
--------------------------------------------------------------------------------

-- | File Context View component
component :: forall q m. MonadAff m => H.Component q Input Output m
component =
  H.mkComponent
    { initialState: \input -> initialState { wsClient = input.wsClient }
    , render
    , eval: H.mkEval $ H.defaultEval
        { handleAction = handleAction
        , initialize = Just Initialize
        }
    }
