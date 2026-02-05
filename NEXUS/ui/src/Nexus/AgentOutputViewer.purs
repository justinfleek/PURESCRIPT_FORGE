-- | Agent Output Viewer - Renders structured agent outputs
-- | Follows Output Format Protocol for displaying agent results
module Nexus.AgentOutputViewer where

import Prelude

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Effect.Aff.Class (class MonadAff)
import Effect.Aff (delay, Milliseconds(..))
import Effect.Class (liftEffect)
import Control.MonadZero (when)
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Either (Either(..))
import Nexus.AgentOutputViewer.Types as Types
import Nexus.AgentOutputViewer.Components as Components
import Nexus.AgentOutputViewer.FFI as FFI

type State =
  { output :: Types.AgentOutput
  , detailsExpanded :: Boolean
  , errorMessage :: Maybe String
  , renderedMarkdown :: Maybe String
  }

data Action
  = Initialize
  | ToggleDetails
  | CopyCommand String
  | ToggleChecklistItem Int
  | DismissError
  | RenderMarkdown String

component :: forall q i o. MonadAff m => H.Component q Types.AgentOutput o m
component = H.mkComponent
  { initialState: \output ->
      { output
      , detailsExpanded: false
      , errorMessage: Nothing
      , renderedMarkdown: Nothing
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (HH.ClassName "agent-output-viewer") ]
    [ renderErrorNotification state.errorMessage
    , Components.renderStatusHeader state.output.status state.output.summary
    , Components.renderEvidenceSection state.output.evidence
    , Components.renderChangesSection state.output.whatChanged
    , Components.renderViolationsSection state.output.violations CopyCommand
    , Components.renderNextStepsSection state.output.nextSteps
    , Components.renderVerificationSection state.output.verification CopyCommand
    , Components.renderCompletionChecklist state.output.completionChecklist
    , renderDetailsSection state.output.details state.detailsExpanded state.renderedMarkdown
    ]

renderErrorNotification :: forall m. Maybe String -> H.ComponentHTML Action () m
renderErrorNotification Nothing = HH.text ""
renderErrorNotification (Just errorMsg) =
  HH.div
    [ HP.class_ (HH.ClassName "error-notification")
    , HP.attr (HH.AttrName "role") "alert"
    ]
    [ HH.div
        [ HP.class_ (HH.ClassName "error-content") ]
        [ HH.span
            [ HP.class_ (HH.ClassName "error-label") ]
            [ HH.text "Error" ]
        , HH.span
            [ HP.class_ (HH.ClassName "error-message") ]
            [ HH.text errorMsg ]
        , HH.button
            [ HP.class_ (HH.ClassName "error-dismiss")
            , HE.onClick \_ -> DismissError
            , HP.attr (HH.AttrName "aria-label") "Dismiss error"
            , HP.type_ HP.ButtonButton
            ]
            [ HH.text "Dismiss" ]
        ]
    ]

renderDetailsSection :: forall m. Maybe String -> Boolean -> Maybe String -> H.ComponentHTML Action () m
renderDetailsSection Nothing _ _ = HH.text ""
renderDetailsSection (Just details) expanded rendered =
  HH.div
    [ HP.class_ (HH.ClassName "details-section") ]
    [ HH.button
        [ HP.class_ (HH.ClassName "toggle-details")
        , HE.onClick \_ -> ToggleDetails
        ]
        [ HH.text (if expanded then "Hide Details" else "Show Details") ]
    , if expanded then
        HH.div
          [ HP.class_ (HH.ClassName "details-content")
          , HP.ref (H.RefLabel "markdown-content")
          ]
          [ HH.text (case rendered of
              Just html -> html  -- HTML rendered markdown
              Nothing -> details  -- Fallback to plain text if markdown not rendered yet
            )
          ]
      else
        HH.text ""
    ]

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> do
    state <- H.get
    -- Render markdown if details exist and component is expanded
    when (state.detailsExpanded) do
      case state.output.details of
        Just details -> do
          rendered <- H.liftAff $ FFI.renderMarkdown details
          H.modify_ \s -> s { renderedMarkdown = Just rendered }
          -- Set innerHTML via FFI after rendering
          void $ H.liftEffect $ FFI.setInnerHTML "markdown-content" rendered
        Nothing -> pure unit
  ToggleDetails -> do
    state <- H.get
    let wasExpanded = state.detailsExpanded
    H.modify_ \s -> s { detailsExpanded = not s.detailsExpanded }
    -- Render markdown when expanding if not already rendered
    when (wasExpanded == false && state.renderedMarkdown == Nothing) do
      case state.output.details of
        Just details -> do
          rendered <- H.liftAff $ FFI.renderMarkdown details
          H.modify_ \s -> s { renderedMarkdown = Just rendered }
          -- Set innerHTML via FFI after rendering
          void $ H.liftEffect $ FFI.setInnerHTML "markdown-content" rendered
        Nothing -> pure unit
  CopyCommand cmd -> do
    result <- H.liftAff $ FFI.copyToClipboard cmd
    case result of
      Left err -> do
        H.modify_ \s -> s { errorMessage = Just ("Clipboard operation failed: " <> err) }
        -- Auto-dismiss error after 5 seconds
        void $ H.fork do
          H.liftAff $ delay (Milliseconds 5000.0)
          H.modify_ \s -> s { errorMessage = Nothing }
      Right _ -> do
        -- Show success briefly (optional)
        H.modify_ \s -> s { errorMessage = Nothing }
  ToggleChecklistItem idx -> do
    H.modify_ \s -> do
      let
        updatedChecklist = case s.output.completionChecklist of
          Just items ->
            case Array.updateAt idx (\item -> item { checked = not item.checked }) items of
              Just updated -> Just updated
              Nothing -> Just items
          Nothing -> Nothing
      in
        s { output { completionChecklist = updatedChecklist } }
  DismissError -> do
    H.modify_ \s -> s { errorMessage = Nothing }
  RenderMarkdown markdown -> do
    rendered <- H.liftAff $ FFI.renderMarkdown markdown
    H.modify_ \s -> s { renderedMarkdown = Just rendered }
