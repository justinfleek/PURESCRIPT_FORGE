-- | Model Selector Component - Compact Model Selection Dropdown
-- |
-- | **What:** Provides a compact dropdown interface for selecting Venice models, with
-- |         quick access to recommended models and full model picker.
-- | **Why:** Enables users to quickly switch between models without opening a full modal,
-- |         while providing access to detailed model selection when needed.
-- | **How:** Renders a dropdown button showing current model, with dropdown menu showing
-- |         quick select options and links to full picker and comparison.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Model`: Model types and catalog
-- |
-- | **Mathematical Foundation:**
-- | - **Model Selection:** Selected model is stored in component state and emitted via output
-- | - **Dropdown State:** Dropdown open/closed state is managed locally
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.ModelSelector as ModelSelector
-- |
-- | -- In parent component:
-- | HH.slot _modelSelector unit ModelSelector.component
-- |   { selectedModel: "llama-3.3-70b" }
-- |   (case _ of
-- |     ModelSelector.ModelSelected id -> HandleModelSelected id)
-- | ```
-- |
-- | Based on spec 16-MODEL-SELECTION.md
module Sidepanel.Components.ModelSelector where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Sidepanel.Model (Model, allModels, findById, getRecommended)
import Sidepanel.Utils.Currency (formatDiem)

-- | Component input
type Input =
  { selectedModel :: String  -- Model ID
  }

-- | Component state
type State =
  { selectedModel :: String
  , isOpen :: Boolean
  , availableModels :: Array Model
  , recommendedModels :: Array Model
  }

-- | Actions
data Action
  = Initialize
  | Receive Input
  | ToggleDropdown
  | CloseDropdown
  | SelectModel String
  | OpenFullPicker
  | OpenComparison

-- | Outputs
data Output
  = ModelSelected String
  | OpenModelPicker
  | OpenModelComparison

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { selectedModel: input.selectedModel
      , isOpen: false
      , availableModels: allModels
      , recommendedModels: getRecommended allModels
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    currentModel = findById state.selectedModel
    modelName = case currentModel of
      Just m -> m.displayName
      Nothing -> state.selectedModel
  in
    HH.div
      [ HP.class_ (H.ClassName "model-selector") ]
      [ HH.button
          [ HP.classes [ H.ClassName "model-selector__button", if state.isOpen then H.ClassName "model-selector__button--open" else H.ClassName "" ]
          , HE.onClick \_ -> ToggleDropdown
          ]
          [ HH.span
              [ HP.class_ (H.ClassName "model-selector__label") ]
              [ HH.text "MODEL: " ]
          , HH.span
              [ HP.class_ (H.ClassName "model-selector__value") ]
              [ HH.text modelName ]
          , HH.span
              [ HP.class_ (H.ClassName "model-selector__arrow") ]
              [ HH.text "▼" ]
          ]
      , if state.isOpen then
          renderDropdown state
        else
          HH.text ""
      ]

renderDropdown :: forall m. State -> H.ComponentHTML Action () m
renderDropdown state =
  HH.div
    [ HP.class_ (H.ClassName "model-selector__dropdown") ]
    [ HH.div
        [ HP.class_ (H.ClassName "dropdown-section") ]
        [ HH.div
            [ HP.class_ (H.ClassName "dropdown-section__title") ]
            [ HH.text "QUICK SELECT" ]
        , HH.div
            [ HP.class_ (H.ClassName "dropdown-section__items") ]
            (map (renderQuickSelectItem state.selectedModel) state.recommendedModels)
        ]
    , HH.div
        [ HP.class_ (H.ClassName "dropdown-section") ]
        [ HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--ghost" ]
            , HE.onClick \_ -> OpenFullPicker
            ]
            [ HH.text "Show All Models..." ]
        , HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--ghost" ]
            , HE.onClick \_ -> OpenComparison
            ]
            [ HH.text "Compare..." ]
        ]
    ]

renderQuickSelectItem :: forall m. String -> Model -> H.ComponentHTML Action () m
renderQuickSelectItem selectedId model =
  let
    isSelected = model.id == selectedId
    badge = case model.size of
      Small -> "Small"
      Medium -> "Medium"
      Large -> "Large"
      XLarge -> "XLarge"
  in
    HH.button
      [ HP.classes
          [ H.ClassName "quick-select-item"
          , if isSelected then H.ClassName "quick-select-item--selected" else H.ClassName ""
          ]
      , HE.onClick \_ -> SelectModel model.id
      ]
      [ HH.span
          [ HP.class_ (H.ClassName "quick-select-item__radio") ]
          [ HH.text $ if isSelected then "●" else "○" ]
      , HH.span
          [ HP.class_ (H.ClassName "quick-select-item__name") ]
          [ HH.text model.displayName ]
      , HH.span
          [ HP.class_ (H.ClassName "quick-select-item__badge") ]
          [ HH.text badge ]
      ]

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize ->
    pure unit
  
  Receive input ->
    H.modify_ _ { selectedModel = input.selectedModel }
  
  ToggleDropdown -> do
    state <- H.get
    H.modify_ _ { isOpen = not state.isOpen }
  
  CloseDropdown ->
    H.modify_ _ { isOpen = false }
  
  SelectModel id -> do
    H.modify_ _ { selectedModel = id, isOpen = false }
    H.raise (ModelSelected id)
  
  OpenFullPicker -> do
    H.modify_ _ { isOpen = false }
    H.raise OpenModelPicker
  
  OpenComparison -> do
    H.modify_ _ { isOpen = false }
    H.raise OpenModelComparison
