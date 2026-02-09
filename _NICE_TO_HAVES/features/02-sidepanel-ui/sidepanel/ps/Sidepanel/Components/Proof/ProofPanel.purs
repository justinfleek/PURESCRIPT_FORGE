-- | Proof Panel Component - Lean4 Proof Assistant Interface
-- |
-- | **What:** Provides an interface for interacting with Lean4 proof assistant, displaying
-- |         proof goals, diagnostics, and suggested tactics. Supports applying tactics
-- |         and searching for theorems.
-- | **Why:** Enables users to work with Lean4 proofs directly from the sidepanel, viewing
-- |         goals, errors, and getting tactic suggestions without leaving their editor.
-- | **How:** Connects to Lean4 LSP via WebSocket, displays goals with context, shows
-- |         diagnostics with severity, and provides tactic suggestions. Supports applying
-- |         tactics and searching for theorems.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: Proof state types
-- | - `Sidepanel.WebSocket.Client`: WebSocket communication
-- | - `Sidepanel.Api.Bridge`: Bridge API methods for Lean operations
-- |
-- | **Mathematical Foundation:**
-- | - **Goal Display:** Goals are displayed with their type and context. Context is
-- |   parsed from string format ("name : type" or "name : type := value").
-- | - **Tactic Application:** Tactics are applied at the current cursor position
-- |   (line, column) in the file.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Proof.ProofPanel as ProofPanel
-- |
-- | -- In parent component:
-- | HH.slot _proof unit ProofPanel.component
-- |   { proofState: appState.proof, wsClient: wsClient }
-- |   (const HandleAppAction)
-- | ```
-- |
-- | Based on spec 61-PROOF-PANEL.md
module Sidepanel.Components.Proof.ProofPanel where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set as Set
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Sidepanel.State.AppState (ProofState, Goal, Diagnostic, Tactic)
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge
import Data.String as String
import Data.String.Pattern (Pattern(..))

-- | Proof goal from Lean
type ProofGoal =
  { index :: Int
  , type_ :: String
  , context :: Array ContextItem
  }

type ContextItem =
  { name :: String
  , type_ :: String
  , value :: Maybe String
  }

-- | Diagnostic severity
data DiagnosticSeverity = Error | Warning | Info | Hint

derive instance eqDiagnosticSeverity :: Eq DiagnosticSeverity

-- | Tactic suggestion
type TacticSuggestion =
  { tactic :: String
  , description :: String
  , confidence :: Number
  }

-- | Component state
type State =
  { connected :: Boolean
  , currentFile :: Maybe String
  , goals :: Array ProofGoal
  , diagnostics :: Array Diagnostic
  , suggestions :: Array TacticSuggestion
  , expandedGoals :: Set.Set Int
  , isLoadingSuggestions :: Boolean
  , wsClient :: Maybe WS.WSClient
  }

-- | Actions
data Action
  = Initialize
  | Receive ProofState
  | ToggleGoalExpand Int
  | ApplyTactic String
  | RefreshGoals
  | SearchTheorems String

-- | Component input
type Input = { proofState :: ProofState, wsClient :: Maybe WS.WSClient }

-- | Component
component :: forall q o m. MonadAff m => H.Component q Input o m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { connected: input.proofState.connected
  , currentFile: input.proofState.currentFile
  , goals: convertGoals input.proofState.goals
  , diagnostics: input.proofState.diagnostics
  , suggestions: convertTactics input.proofState.suggestedTactics
  , expandedGoals: Set.singleton 0
  , isLoadingSuggestions: false
  , wsClient: input.wsClient
  }

convertGoals :: Array Goal -> Array ProofGoal
convertGoals = Array.mapWithIndex \index goal ->
  { index
  , type_: goal.type_
  , context: parseContext goal.context
  }

parseContext :: String -> Array ContextItem
parseContext ctx =
  -- Parse context string (format: "name : type" or "name : type := value")
  -- Split by lines, then parse each line
  let lines = String.split (Pattern "\n") ctx
  in
    Array.catMaybes $ map parseContextLine lines
  where
    parseContextLine :: String -> Maybe ContextItem
    parseContextLine line =
      -- Parse format: "name : type" or "name : type := value"
      case String.split (Pattern " : ") line of
        [name, rest] ->
          case String.split (Pattern " := ") rest of
            [type_, value] -> Just { name: String.trim name, type_: String.trim type_, value: Just (String.trim value) }
            [type_] -> Just { name: String.trim name, type_: String.trim type_, value: Nothing }
            _ -> Nothing
        _ -> Nothing

convertTactics :: Array Tactic -> Array TacticSuggestion
convertTactics = map \tactic ->
  { tactic: tactic.name
  , description: tactic.description
  , confidence: tactic.confidence
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "proof-panel") ]
    [ renderHeader state
    , renderCurrentFile state.currentFile
    , renderGoals state
    , renderDiagnostics state.diagnostics
    , renderSuggestions state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "proof-panel__header") ]
    [ HH.h2_ [ HH.text "Proof Status" ]
    , HH.div
        [ HP.classes $ connectionClasses state.connected ]
        [ HH.span [ HP.class_ (H.ClassName "connection-dot") ] []
        , HH.text $ if state.connected then "Connected (Lean)" else "Disconnected"
        ]
    ]

connectionClasses :: Boolean -> Array H.ClassName
connectionClasses connected =
  [ H.ClassName "connection-status" ] <>
    if connected
      then [ H.ClassName "connection-status--connected" ]
      else [ H.ClassName "connection-status--disconnected" ]

renderCurrentFile :: forall m. Maybe String -> H.ComponentHTML Action () m
renderCurrentFile = case _ of
  Nothing ->
    HH.div
      [ HP.classes [ H.ClassName "proof-panel__file", H.ClassName "proof-panel__file--none" ] ]
      [ HH.text "No Lean file open" ]
  Just file ->
    HH.div
      [ HP.class_ (H.ClassName "proof-panel__file") ]
      [ HH.text $ "Current File: " <> file ]

renderGoals :: forall m. State -> H.ComponentHTML Action () m
renderGoals state =
  HH.section
    [ HP.class_ (H.ClassName "proof-panel__goals") ]
    [ HH.div
        [ HP.class_ (H.ClassName "section-header") ]
        [ HH.text $ "Goals (" <> show (Array.length state.goals) <> ")" ]
    , if Array.null state.goals
        then HH.div
          [ HP.class_ (H.ClassName "goals-empty") ]
          [ HH.text "✓ No goals - proof complete!" ]
        else HH.div
          [ HP.class_ (H.ClassName "goals-list") ]
          (Array.mapWithIndex (renderGoal state.expandedGoals) state.goals)
    ]

renderGoal :: forall m. Set.Set Int -> Int -> ProofGoal -> H.ComponentHTML Action () m
renderGoal expandedSet index goal =
  let isExpanded = Set.member index expandedSet
  in
    HH.div
      [ HP.classes
          [ H.ClassName "goal-card"
          , if isExpanded then H.ClassName "goal-card--expanded" else H.ClassName ""
          ]
      , HE.onClick \_ -> ToggleGoalExpand index
      ]
      [ HH.div
          [ HP.class_ (H.ClassName "goal-card__header") ]
          [ HH.span [ HP.class_ (H.ClassName "goal-card__title") ]
              [ HH.text $ "Goal " <> show (index + 1) ]
          , HH.span [ HP.class_ (H.ClassName "goal-card__expand") ]
              [ HH.text $ if isExpanded then "▼" else "▶" ]
          ]
      , HH.div
          [ HP.class_ (H.ClassName "goal-card__type") ]
          [ HH.code_ [ HH.text $ "⊢ " <> goal.type_ ] ]
      , if isExpanded then
          HH.div
            [ HP.class_ (H.ClassName "goal-card__context") ]
            [ HH.div [ HP.class_ (H.ClassName "context-title") ] [ HH.text "Context:" ]
            , HH.div
                [ HP.class_ (H.ClassName "context-items") ]
                (map renderContextItem goal.context)
            ]
        else
          HH.text ""
      ]

renderContextItem :: forall m. ContextItem -> H.ComponentHTML Action () m
renderContextItem { name, type_, value } =
  HH.div
    [ HP.class_ (H.ClassName "context-item") ]
    [ HH.code_
        [ HH.span [ HP.class_ (H.ClassName "context-name") ] [ HH.text name ]
        , HH.text " : "
        , HH.span [ HP.class_ (H.ClassName "context-type") ] [ HH.text type_ ]
        , case value of
            Just v -> HH.span_ [ HH.text $ " := " <> v ]
            Nothing -> HH.text ""
        ]
    ]

renderDiagnostics :: forall m. Array Diagnostic -> H.ComponentHTML Action () m
renderDiagnostics diagnostics =
  if not (Array.null diagnostics) then
    HH.section
      [ HP.class_ (H.ClassName "proof-panel__diagnostics") ]
      [ HH.div [ HP.class_ (H.ClassName "section-header") ] [ HH.text "Diagnostics" ]
      , HH.div
          [ HP.class_ (H.ClassName "diagnostics-list") ]
          (map renderDiagnostic diagnostics)
      ]
  else
    HH.text ""

renderDiagnostic :: forall m. Diagnostic -> H.ComponentHTML Action () m
renderDiagnostic diag =
  let severity = parseSeverity diag.severity
  in
    HH.div
      [ HP.classes $ diagnosticClasses severity ]
      [ HH.span [ HP.class_ (H.ClassName "diagnostic-icon") ]
          [ HH.text $ severityIcon severity ]
      , HH.span [ HP.class_ (H.ClassName "diagnostic-location") ]
          [ HH.text $ "Line " <> show diag.range.start.line <> ": " ]
      , HH.span [ HP.class_ (H.ClassName "diagnostic-message") ]
          [ HH.text diag.message ]
      ]

parseSeverity :: String -> DiagnosticSeverity
parseSeverity s = case s of
  "error" -> Error
  "warning" -> Warning
  "info" -> Info
  "hint" -> Hint
  _ -> Warning

severityIcon :: DiagnosticSeverity -> String
severityIcon = case _ of
  Error -> "✗"
  Warning -> "⚠"
  Info -> "ℹ"
  Hint -> "💡"

diagnosticClasses :: DiagnosticSeverity -> Array H.ClassName
diagnosticClasses severity =
  [ H.ClassName "diagnostic-item" ] <> case severity of
    Error -> [ H.ClassName "diagnostic-item--error" ]
    Warning -> [ H.ClassName "diagnostic-item--warning" ]
    Info -> [ H.ClassName "diagnostic-item--info" ]
    Hint -> [ H.ClassName "diagnostic-item--hint" ]

renderSuggestions :: forall m. State -> H.ComponentHTML Action () m
renderSuggestions state =
  HH.section
    [ HP.class_ (H.ClassName "proof-panel__suggestions") ]
    [ HH.div [ HP.class_ (H.ClassName "section-header") ] [ HH.text "Suggested Tactics" ]
    , if state.isLoadingSuggestions
        then HH.div [ HP.class_ (H.ClassName "suggestions-loading") ]
          [ HH.text "Analyzing..." ]
        else if Array.null state.suggestions
          then HH.div [ HP.class_ (H.ClassName "suggestions-empty") ]
            [ HH.text "No suggestions available" ]
          else HH.div
            [ HP.class_ (H.ClassName "suggestions-list") ]
            (map renderSuggestion state.suggestions)
    ]

renderSuggestion :: forall m. TacticSuggestion -> H.ComponentHTML Action () m
renderSuggestion { tactic, description } =
  HH.div
    [ HP.class_ (H.ClassName "suggestion-item")
    , HE.onClick \_ -> ApplyTactic tactic
    ]
    [ HH.code [ HP.class_ (H.ClassName "suggestion-tactic") ] [ HH.text tactic ]
    , HH.span [ HP.class_ (H.ClassName "suggestion-description") ] [ HH.text description ]
    ]

handleAction :: forall m o. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive proofState ->
    H.modify_ \s ->
      s { connected = proofState.connected
        , currentFile = proofState.currentFile
        , goals = convertGoals proofState.goals
        , diagnostics = proofState.diagnostics
        , suggestions = convertTactics proofState.suggestedTactics
        }

  ToggleGoalExpand index ->
    H.modify_ \s ->
      s { expandedGoals =
          if Set.member index s.expandedGoals
            then Set.delete index s.expandedGoals
            else Set.insert index s.expandedGoals
        }

  ApplyTactic tactic -> do
    state <- H.get
    case state.wsClient, state.currentFile of
      Just client, Just file -> do
        -- Apply tactic at current cursor position (default to line 0, column 0)
        result <- H.liftAff $ Bridge.applyLeanTactic client 
          { file: file
          , line: 0
          , column: 0
          , tactic: tactic
          , goalIndex: Nothing
          }
        case result of
          Right response -> do
            if response.success then
              -- Refresh goals after successful tactic application
              RefreshGoals
            else
              -- Show error message (would be displayed in UI)
              pure unit
          Left _ -> pure unit
      _, _ -> pure unit

  RefreshGoals -> do
    state <- H.get
    case state.wsClient, state.currentFile of
      Just client, Just file -> do
        -- Get goals at cursor position (default to line 0, column 0)
        result <- H.liftAff $ Bridge.getLeanGoals client { file: file, line: 0, column: 0 }
        case result of
          Right response -> do
            -- Convert LeanGoal from Bridge API to ProofGoal
            let goals = map (\g -> { index: 0, type_: g.type_, context: map (\c -> { name: c.name, type_: c.type_, value: Nothing }) g.context }) response.goals
            H.modify_ _ { goals = goals }
            -- Also check file for diagnostics
            checkResult <- H.liftAff $ Bridge.checkLeanFile client { file: file }
            case checkResult of
              Right checkResponse -> do
                -- Convert LeanDiagnostic from Bridge API to Diagnostic
                let diagnostics = map (\d -> 
                      { severity: d.severity
                      , message: d.message
                      , range: { start: { line: d.range.start.line, character: d.range.start.col }, end: { line: d.range.end.line, character: d.range.end.col } }
                      }
                    ) checkResponse.diagnostics
                H.modify_ _ { diagnostics = diagnostics }
              Left _ -> pure unit
          Left err -> pure unit  -- Handle error
      _, _ -> pure unit

  SearchTheorems query -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.searchLeanTheorems client
          { query: query
          , limit: Just 20
          , file: state.currentFile
          }
        case result of
          Right response -> do
            -- Convert TheoremResult to TacticSuggestion for display
            let suggestions = map (\t -> 
                  { tactic: t.name
                  , description: fromMaybe t.statement t.description
                  , confidence: 0.8  -- Default confidence
                  }
                ) response.theorems
            H.modify_ _ { suggestions = suggestions }
          Left _ -> pure unit
      Nothing -> pure unit
