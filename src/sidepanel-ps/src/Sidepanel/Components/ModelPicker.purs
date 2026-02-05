-- | Model Picker Component - Full Model Selection Modal
-- |
-- | **What:** Provides a full-screen modal interface for browsing, filtering, and selecting
-- |         Venice models with detailed information, search, and filtering capabilities.
-- | **Why:** Enables users to make informed model selections by viewing detailed specifications,
-- |         comparing models, and filtering by size, speed, and quality.
-- | **How:** Renders a modal with filters, search, featured models section, and categorized
-- |         model list. Supports model selection and comparison.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Model`: Model types and catalog
-- |
-- | **Mathematical Foundation:**
-- | - **Filtering:** Models are filtered by size, speed tier, and search query
-- | - **Grouping:** Models are grouped by size category for display
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.ModelPicker as ModelPicker
-- |
-- | -- In parent component:
-- | HH.slot _modelPicker unit ModelPicker.component
-- |   { selectedModel: "llama-3.3-70b", visible: true }
-- |   (case _ of
-- |     ModelPicker.ModelSelected id -> HandleModelSelected id
-- |     ModelPicker.Close -> HandleClosePicker)
-- | ```
-- |
-- | Based on spec 16-MODEL-SELECTION.md
module Sidepanel.Components.ModelPicker where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Int as Int
import Sidepanel.Model (Model, allModels, ModelSize(..), SpeedTier(..), QualityTier(..), filterBySize, searchModels, getRecommended, showModelSize, showSpeedTier, showQualityTier)
import Sidepanel.Utils.Currency (formatDiem, formatNumber)

-- | Component input
type Input =
  { selectedModel :: String
  , visible :: Boolean
  }

-- | Component state
type State =
  { selectedModel :: String
  , visible :: Boolean
  , allModels :: Array Model
  , filteredModels :: Array Model
  , searchQuery :: String
  , sizeFilter :: Maybe ModelSize
  , speedFilter :: Maybe SpeedTier
  }

-- | Actions
data Action
  = Initialize
  | Receive Input
  | Close
  | SelectModel String
  | SetSearchQuery String
  | SetSizeFilter (Maybe ModelSize)
  | SetSpeedFilter (Maybe SpeedTier)
  | OpenComparison String String  -- model1, model2

-- | Outputs
data Output
  = ModelSelected String
  = ClosePicker
  = OpenComparisonView String String

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { selectedModel: input.selectedModel
      , visible: input.visible
      , allModels: allModels
      , filteredModels: allModels
      , searchQuery: ""
      , sizeFilter: Nothing
      , speedFilter: Nothing
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
  if state.visible then
    HH.div
      [ HP.class_ (H.ClassName "model-picker-modal") ]
      [ HH.div
          [ HP.class_ (H.ClassName "modal__overlay")
          , HE.onClick \_ -> Close
          ]
          []
      , HH.div
          [ HP.class_ (H.ClassName "modal__content") ]
          [ renderHeader
          , renderFilters state
          , renderFeatured state
          , renderAllModels state
          ]
      ]
  else
    HH.text ""

renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.header
    [ HP.class_ (H.ClassName "model-picker__header") ]
    [ HH.h2_ [ HH.text "SELECT MODEL" ]
    , HH.button
        [ HP.class_ (H.ClassName "modal__close")
        , HE.onClick \_ -> Close
        , HP.attr (H.AttrName "aria-label") "Close"
        ]
        [ HH.text "✕" ]
    ]

renderFilters :: forall m. State -> H.ComponentHTML Action () m
renderFilters state =
  HH.div
    [ HP.class_ (H.ClassName "model-picker__filters") ]
    [ HH.select
        [ HP.class_ (H.ClassName "filter-select")
        , HE.onValueChange \v -> SetSizeFilter $ parseSizeFilter v
        ]
        [ HH.option [ HP.value "" ] [ HH.text "All Sizes" ]
        , HH.option [ HP.value "small" ] [ HH.text "Small" ]
        , HH.option [ HP.value "medium" ] [ HH.text "Medium" ]
        , HH.option [ HP.value "large" ] [ HH.text "Large" ]
        , HH.option [ HP.value "xlarge" ] [ HH.text "XLarge" ]
        ]
    , HH.select
        [ HP.class_ (H.ClassName "filter-select")
        , HE.onValueChange \v -> SetSpeedFilter $ parseSpeedFilter v
        ]
        [ HH.option [ HP.value "" ] [ HH.text "All Speeds" ]
        , HH.option [ HP.value "slow" ] [ HH.text "Slow" ]
        , HH.option [ HP.value "medium" ] [ HH.text "Medium" ]
        , HH.option [ HP.value "fast" ] [ HH.text "Fast" ]
        , HH.option [ HP.value "veryfast" ] [ HH.text "Very Fast" ]
        ]
    , HH.input
        [ HP.type_ HP.InputText
        , HP.class_ (H.ClassName "filter-search")
        , HP.placeholder "🔍 Search..."
        , HP.value state.searchQuery
        , HE.onValueInput SetSearchQuery
        ]
    ]

parseSizeFilter :: String -> Maybe ModelSize
parseSizeFilter = case _ of
  "small" -> Just Small
  "medium" -> Just Medium
  "large" -> Just Large
  "xlarge" -> Just XLarge
  _ -> Nothing

parseSpeedFilter :: String -> Maybe SpeedTier
parseSpeedFilter = case _ of
  "slow" -> Just Slow
  "medium" -> Just Medium
  "fast" -> Just Fast
  "veryfast" -> Just VeryFast
  _ -> Nothing

renderFeatured :: forall m. State -> H.ComponentHTML Action () m
renderFeatured state =
  let
    recommended = getRecommended state.filteredModels
  in
    if not (Array.null recommended) then
      HH.div
        [ HP.class_ (H.ClassName "model-picker__featured") ]
        [ HH.h3_ [ HH.text "FEATURED" ]
        , HH.div
            [ HP.class_ (H.ClassName "featured-models") ]
            (map (renderModelCard state.selectedModel) recommended)
        ]
    else
      HH.text ""

renderAllModels :: forall m. State -> H.ComponentHTML Action () m
renderAllModels state =
  let
    grouped = groupBySize state.filteredModels
  in
    HH.div
      [ HP.class_ (H.ClassName "model-picker__all-models") ]
      [ HH.h3_ [ HH.text "ALL MODELS" ]
      , HH.div
          [ HP.class_ (H.ClassName "model-groups") ]
          (Array.map renderSizeGroup grouped)
      ]

type SizeGroup = { size :: ModelSize, models :: Array Model }

groupBySize :: Array Model -> Array SizeGroup
groupBySize models =
  let
    sizes = [ XLarge, Large, Medium, Small ]
  in
    Array.mapMaybe (\size ->
      let sizeModels = filterBySize size models
      in if Array.null sizeModels then Nothing
         else Just { size, models: sizeModels }
    ) sizes

renderSizeGroup :: forall m. SizeGroup -> H.ComponentHTML Action () m
renderSizeGroup { size, models } =
  HH.div
    [ HP.class_ (H.ClassName "model-group") ]
    [ HH.h4
        [ HP.class_ (H.ClassName "model-group__title") ]
        [ HH.text $ showModelSize size <> " (" <> show (Array.length models) <> ")" ]
    , HH.div
        [ HP.class_ (H.ClassName "model-group__items") ]
        (map (renderModelCard "") models)  -- No selected model in group view
    ]

renderModelCard :: forall m. String -> Model -> H.ComponentHTML Action () m
renderModelCard selectedId model =
  let
    isSelected = model.id == selectedId
  in
    HH.div
      [ HP.classes
          [ H.ClassName "model-card"
          , if isSelected then H.ClassName "model-card--selected" else H.ClassName ""
          , if model.isRecommended then H.ClassName "model-card--recommended" else H.ClassName ""
          ]
      ]
      [ if model.isRecommended then
          HH.div
            [ HP.class_ (H.ClassName "model-card__badge") ]
            [ HH.text "⭐ RECOMMENDED" ]
        else
          HH.text ""
      , HH.div
          [ HP.class_ (H.ClassName "model-card__name") ]
          [ HH.text model.displayName ]
      , HH.div
          [ HP.class_ (H.ClassName "model-card__description") ]
          [ HH.text $ String.joinWith ", " model.bestFor ]
      , HH.div
          [ HP.class_ (H.ClassName "model-card__stats") ]
          [ renderStat "Speed" (showSpeedTier model.speed)
          , renderStat "Quality" (showQualityTier model.quality)
          , renderStat "Context" (formatNumber (Int.toNumber model.contextWindow) <> " tokens")
          , renderStat "Cost" (formatDiem model.pricing.inputPer1K <> "/1K tokens")
          ]
      , HH.div
          [ HP.class_ (H.ClassName "model-card__best-for") ]
          [ HH.text $ "Best for: " <> String.joinWith ", " model.bestFor ]
      , HH.button
          [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary" ]
          , HE.onClick \_ -> SelectModel model.id
          ]
          [ HH.text $ if isSelected then "Selected" else "Select" ]
      ]

renderStat :: forall m. String -> String -> H.ComponentHTML Action () m
renderStat label value =
  HH.div
    [ HP.class_ (H.ClassName "model-stat") ]
    [ HH.span
        [ HP.class_ (H.ClassName "model-stat__label") ]
        [ HH.text $ label <> ": " ]
    , HH.span
        [ HP.class_ (H.ClassName "model-stat__value") ]
        [ HH.text value ]
    ]

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize ->
    pure unit
  
  Receive input -> do
    H.modify_ _
      { selectedModel = input.selectedModel
      , visible = input.visible
      }
    applyFilters
  
  Close -> do
    H.modify_ _ { visible = false }
    H.raise ClosePicker
  
  SelectModel id -> do
    H.modify_ _ { selectedModel = id, visible = false }
    H.raise (ModelSelected id)
  
  SetSearchQuery query -> do
    H.modify_ _ { searchQuery = query }
    applyFilters
  
  SetSizeFilter size -> do
    H.modify_ _ { sizeFilter = size }
    applyFilters
  
  SetSpeedFilter speed -> do
    H.modify_ _ { speedFilter = speed }
    applyFilters
  
  OpenComparison id1 id2 -> do
    H.raise (OpenComparisonView id1 id2)

-- | Apply filters - Update filtered models based on current filters
applyFilters :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
applyFilters = do
  state <- H.get
  let
    -- Start with all models
    filtered = if String.null state.searchQuery
      then state.allModels
      else searchModels state.searchQuery state.allModels
    
    -- Apply size filter
    sizeFiltered = case state.sizeFilter of
      Just size -> filterBySize size filtered
      Nothing -> filtered
    
    -- Apply speed filter
    speedFiltered = case state.speedFilter of
      Just speed -> Array.filter (\m -> m.speed == speed) sizeFiltered
      Nothing -> sizeFiltered
  
  H.modify_ _ { filteredModels = speedFiltered }
