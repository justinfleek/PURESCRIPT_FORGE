-- | Model Comparison Component - Side-by-Side Model Comparison
-- |
-- | **What:** Provides a modal interface for comparing two models side-by-side, showing
-- |         differences in parameters, context, speed, quality, cost, and use cases.
-- | **Why:** Helps users make informed decisions by directly comparing model characteristics
-- |         and identifying which model is best suited for their specific use case.
-- | **How:** Renders a comparison table with two models, highlighting differences and
-- |         providing recommendations based on use case.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Model`: Model types and comparison utilities
-- |
-- | **Mathematical Foundation:**
-- | - **Comparison:** Uses `compareModels` to generate comparison data
-- | - **Recommendation:** Recommends model based on differences and use case
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.ModelComparison as ModelComparison
-- |
-- | -- In parent component:
-- | HH.slot _comparison unit ModelComparison.component
-- |   { model1Id: "llama-3.3-70b", model2Id: "deepseek-r1-70b", visible: true }
-- |   (case _ of
-- |     ModelComparison.ModelSelected id -> HandleModelSelected id
-- |     ModelComparison.Close -> HandleCloseComparison)
-- | ```
-- |
-- | Based on spec 16-MODEL-SELECTION.md
module Sidepanel.Components.ModelComparison where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Int as Int
import Data.String as String
import Sidepanel.Model (Model, allModels, findById, compareModels, ModelComparison, showModelSize, showSpeedTier, showQualityTier)
import Sidepanel.Utils.Currency (formatDiem, formatNumber)

-- | Component input
type Input =
  { model1Id :: String
  , model2Id :: String
  , visible :: Boolean
  }

-- | Component state
type State =
  { model1 :: Maybe Model
  , model2 :: Maybe Model
  , comparison :: Maybe ModelComparison
  , visible :: Boolean
  }

-- | Actions
data Action
  = Initialize
  | Receive Input
  | Close
  | SelectModel1
  | SelectModel2
  | SwapModels

-- | Outputs
data Output
  = ModelSelected String
  = CloseComparison

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      let
        m1 = findById input.model1Id
        m2 = findById input.model2Id
        comp = case m1, m2 of
          Just model1, Just model2 -> Just (compareModels model1 model2)
          _, _ -> Nothing
      in
        { model1: m1
        , model2: m2
        , comparison: comp
        , visible: input.visible
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
    case state.model1, state.model2 of
      Just m1, Just m2 ->
        HH.div
          [ HP.class_ (H.ClassName "model-comparison-modal") ]
          [ HH.div
              [ HP.class_ (H.ClassName "modal__overlay")
              , HE.onClick \_ -> Close
              ]
              []
          , HH.div
              [ HP.class_ (H.ClassName "modal__content") ]
              [ renderHeader
              , renderComparison m1 m2
              , renderRecommendation m1 m2
              , renderActions m1 m2
              ]
          ]
      _, _ ->
        HH.div
          [ HP.class_ (H.ClassName "model-comparison-modal") ]
          [ HH.div
              [ HP.class_ (H.ClassName "modal__content") ]
              [ HH.p_ [ HH.text "Error: One or both models not found" ]
              , HH.button
                  [ HP.class_ (H.ClassName "btn")
                  , HE.onClick \_ -> Close
                  ]
                  [ HH.text "Close" ]
              ]
          ]
  else
    HH.text ""

renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.header
    [ HP.class_ (H.ClassName "comparison__header") ]
    [ HH.h2_ [ HH.text "COMPARE MODELS" ]
    , HH.button
        [ HP.class_ (H.ClassName "modal__close")
        , HE.onClick \_ -> Close
        , HP.attr (H.AttrName "aria-label") "Close"
        ]
        [ HH.text "✕" ]
    ]

renderComparison :: forall m. Model -> Model -> H.ComponentHTML Action () m
renderComparison m1 m2 =
  HH.div
    [ HP.class_ (H.ClassName "comparison__table") ]
    [ renderComparisonRow "Parameters" (show m1.parameters <> "B") (show m2.parameters <> "B")
    , renderComparisonRow "Context" (formatNumber (Int.toNumber m1.contextWindow) <> " tokens") (formatNumber (Int.toNumber m2.contextWindow) <> " tokens")
    , renderComparisonRow "Speed" (showSpeedTier m1.speed) (showSpeedTier m2.speed)
    , renderComparisonRow "Quality" (showQualityTier m1.quality) (showQualityTier m2.quality)
    , renderComparisonRow "Cost/1K tokens" (formatDiem m1.pricing.inputPer1K) (formatDiem m2.pricing.inputPer1K)
    , renderComparisonRow "Best For" (String.joinWith ", " m1.bestFor) (String.joinWith ", " m2.bestFor)
    , renderComparisonRow "Weaknesses" (String.joinWith ", " m1.weaknesses) (String.joinWith ", " m2.weaknesses)
    ]

renderComparisonRow :: forall m. String -> String -> String -> H.ComponentHTML Action () m
renderComparisonRow label value1 value2 =
  HH.div
    [ HP.class_ (H.ClassName "comparison-row") ]
    [ HH.div
        [ HP.class_ (H.ClassName "comparison-row__label") ]
        [ HH.text label ]
    , HH.div
        [ HP.class_ (H.ClassName "comparison-row__value") ]
        [ HH.text value1 ]
    , HH.div
        [ HP.class_ (H.ClassName "comparison-row__value") ]
        [ HH.text value2 ]
    ]

renderRecommendation :: forall m. Model -> Model -> H.ComponentHTML Action () m
renderRecommendation m1 m2 =
  let
    recommendation = getRecommendation m1 m2
  in
    HH.div
      [ HP.class_ (H.ClassName "comparison__recommendation") ]
      [ HH.span
          [ HP.class_ (H.ClassName "recommendation-icon") ]
          [ HH.text "💡" ]
      , HH.span
          [ HP.class_ (H.ClassName "recommendation-text") ]
          [ HH.text recommendation ]
      ]

getRecommendation :: Model -> Model -> String
getRecommendation m1 m2 =
  -- Simple recommendation logic (would be more sophisticated in production)
  if m1.isRecommended && not m2.isRecommended then
    "For most tasks, " <> m1.displayName <> " is recommended."
  else if m2.isRecommended && not m1.isRecommended then
    "For most tasks, " <> m2.displayName <> " is recommended."
  else if m1.parameters > m2.parameters then
    m1.displayName <> " has more parameters and may be better for complex tasks."
  else if m2.parameters > m1.parameters then
    m2.displayName <> " has more parameters and may be better for complex tasks."
  else
    "Both models are similar. Choose based on your specific use case."

renderActions :: forall m. Model -> Model -> H.ComponentHTML Action () m
renderActions m1 m2 =
  HH.div
    [ HP.class_ (H.ClassName "comparison__actions") ]
    [ HH.button
        [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary" ]
        , HE.onClick \_ -> SelectModel1
        ]
        [ HH.text $ "Select " <> m1.displayName ]
    , HH.button
        [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary" ]
        , HE.onClick \_ -> SelectModel2
        ]
        [ HH.text $ "Select " <> m2.displayName ]
    , HH.button
        [ HP.classes [ H.ClassName "btn", H.ClassName "btn--ghost" ]
        , HE.onClick \_ -> SwapModels
        ]
        [ HH.text "Swap" ]
    ]

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize ->
    pure unit
  
  Receive input -> do
    let
      m1 = findById input.model1Id
      m2 = findById input.model2Id
      comp = case m1, m2 of
        Just model1, Just model2 -> Just (compareModels model1 model2)
        _, _ -> Nothing
    H.modify_ _
      { model1 = m1
      , model2 = m2
      , comparison = comp
      , visible = input.visible
      }
  
  Close -> do
    H.modify_ _ { visible = false }
    H.raise CloseComparison
  
  SelectModel1 -> do
    state <- H.get
    case state.model1 of
      Just m -> do
        H.modify_ _ { visible = false }
        H.raise (ModelSelected m.id)
      Nothing -> pure unit
  
  SelectModel2 -> do
    state <- H.get
    case state.model2 of
      Just m -> do
        H.modify_ _ { visible = false }
        H.raise (ModelSelected m.id)
      Nothing -> pure unit
  
  SwapModels -> do
    state <- H.get
    let
      newM1 = state.model2
      newM2 = state.model1
      newComp = case newM1, newM2 of
        Just model1, Just model2 -> Just (compareModels model1 model2)
        _, _ -> Nothing
    H.modify_ _
      { model1 = newM1
      , model2 = newM2
      , comparison = newComp
      }
