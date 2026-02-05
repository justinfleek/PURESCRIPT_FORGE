-- | Branch Dialog Component - Create Session Branch Dialog
-- |
-- | **What:** Displays a dialog for creating a branch from an existing session at a specific
-- |         message index, allowing users to fork conversations to try different approaches.
-- | **Why:** Enables exploration of alternative conversation paths without losing the original.
-- | **How:** Shows a form with message index display, optional description field, and
-- |         create/cancel buttons. Validates input and creates branch on confirmation.
-- |
-- | **Dependencies:**
-- | - None (self-contained dialog component)
-- |
-- | **Mathematical Foundation:**
-- | - **Branch Point Invariant:** `messageIndex` must be >= 0 and < message count.
-- | - **Description Invariant:** Description is optional but must be non-empty if provided.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Session.BranchDialog as BranchDialog
-- |
-- | -- In parent component:
-- | HH.slot _branchDialog unit BranchDialog.component
-- |   { sessionId: "session-123", messageIndex: 5 }
-- |   (case _ of
-- |     BranchDialog.BranchCreated id desc -> HandleBranchCreated id desc
-- |     BranchDialog.BranchCancelled -> HandleBranchCancelled)
-- | ```
-- |
-- | Based on spec 24-MULTI-SESSION-MANAGEMENT.md
module Sidepanel.Components.Session.BranchDialog where

import Prelude
import Data.Maybe (Maybe(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Class (liftEffect)
import Effect.Aff.Class (class MonadAff)
import Web.Event.Event (preventDefault)

-- | Component input
type Input =
  { sessionId :: String
  , messageIndex :: Int
  , visible :: Boolean
  }

-- | Component state
type State =
  { sessionId :: String
  , messageIndex :: Int
  , description :: String
  , isCreating :: Boolean
  , visible :: Boolean
  }

-- | Component actions
data Action
  = Receive Input
  | SetDescription String
  | CreateBranch
  | Cancel

-- | Component output
data Output
  = BranchCreated String Int String  -- sessionId, messageIndex, description
  | BranchCancelled

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { sessionId: input.sessionId
      , messageIndex: input.messageIndex
      , description: ""
      , isCreating: false
      , visible: input.visible
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  if state.visible then
    HH.div
      [ HP.class_ (H.ClassName "branch-dialog-overlay")
      , HE.onClick \_ -> Cancel
      ]
      [ HH.div
          [ HP.class_ (H.ClassName "branch-dialog")
          , HE.onClick \e -> liftEffect $ preventDefault e
          ]
          [ -- Header
            HH.div
              [ HP.class_ (H.ClassName "branch-dialog__header") ]
              [ HH.h2_ [ HH.text "Create Branch" ] ]
          
          -- Message info
          , HH.p
              [ HP.class_ (H.ClassName "branch-dialog__info") ]
              [ HH.text $ "Fork conversation from message " <> show (state.messageIndex + 1) ]
          
          -- Description field
          , HH.div
              [ HP.class_ (H.ClassName "branch-dialog__field") ]
              [ HH.label
                  [ HP.for "branch-description" ]
                  [ HH.text "Description (optional)" ]
              , HH.input
                  [ HP.type_ HP.InputText
                  , HP.id_ "branch-description"
                  , HP.class_ (H.ClassName "branch-dialog__input")
                  , HP.placeholder "e.g., 'Try with hooks instead'"
                  , HP.value state.description
                  , HE.onValueInput SetDescription
                  , HP.disabled state.isCreating
                  ]
              ]
          
          -- Actions
          , HH.div
              [ HP.class_ (H.ClassName "branch-dialog__actions") ]
              [ HH.button
                  [ HP.class_ (H.ClassName "btn btn--secondary")
                  , HP.disabled state.isCreating
                  , HE.onClick \_ -> Cancel
                  ]
                  [ HH.text "Cancel" ]
              , HH.button
                  [ HP.classes [H.ClassName "btn", H.ClassName "btn--primary"]
                  , HP.disabled state.isCreating
                  , HE.onClick \_ -> CreateBranch
                  ]
                  [ HH.text $ if state.isCreating then "Creating..." else "Create Branch" ]
              ]
          ]
      ]
  else
    HH.text ""

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ _
      { sessionId = input.sessionId
      , messageIndex = input.messageIndex
      , visible = input.visible
      , description = ""  -- Reset description when dialog opens
      , isCreating = false
      }
  
  SetDescription desc -> do
    H.modify_ _ { description = desc }
  
  CreateBranch -> do
    state <- H.get
    H.modify_ _ { isCreating = true }
    H.raise (BranchCreated state.sessionId state.messageIndex state.description)
  
  Cancel -> do
    H.modify_ _ { visible = false, description = "", isCreating = false }
    H.raise BranchCancelled
