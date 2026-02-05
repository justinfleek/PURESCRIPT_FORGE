{-|
Module      : Sidepanel.Components.CodeReview.CodeReview
Description : Main Halogen component for code review UI

Displays code review issues with severity indicators, fix suggestions, and real-time feedback.
-}
module Sidepanel.Components.CodeReview.CodeReview where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Sidepanel.Components.CodeReview.CodeReviewTypes
  ( CodeReviewResult
  , CodeReviewIssue
  , Severity(..)
  , IssueCategory(..)
  , QualityScore
  , ImprovementSuggestion
  , CodeFix
  )
import Sidepanel.Components.CodeReview.CodeReviewEngine (reviewCode)

-- | Component state
type State =
  { currentResult :: Maybe CodeReviewResult
  , selectedIssue :: Maybe CodeReviewIssue
  , filterSeverity :: Maybe Severity
  , filterCategory :: Maybe IssueCategory
  , loading :: Boolean
  , autoReview :: Boolean  -- Auto-review on file change
  }

-- | Component actions
data Action
  = Initialize
  | ReviewFile String String  -- filePath, content
  | IssueSelected CodeReviewIssue
  | SeverityFilterChanged (Maybe Severity)
  | CategoryFilterChanged (Maybe IssueCategory)
  | ApplyFix CodeFix
  | DismissIssue CodeReviewIssue
  | ToggleAutoReview
  | RefreshReview

-- | Component output
data Output
  = FixApplied CodeFix
  | IssueDismissed CodeReviewIssue
  | ReviewCompleted CodeReviewResult

-- | Component input
type Input =
  { filePath :: Maybe String
  , content :: Maybe String
  }

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { currentResult: Nothing
      , selectedIssue: Nothing
      , filterSeverity: Nothing
      , filterCategory: Nothing
      , loading: false
      , autoReview: true
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "code-review theme-card") ]
    [ renderHeader state
    , renderQualityScore state.currentResult
    , renderFilters state
    , renderIssuesList state
    , renderIssueDetail state.selectedIssue
    , renderSuggestions state.currentResult
    ]

-- | Render header with controls
renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ HP.class_ (H.ClassName "code-review-header") ]
    [ HH.h2
        [ HP.class_ (H.ClassName "code-review-title theme-card-title") ]
        [ HH.text "Code Review" ]
    , HH.div
        [ HP.class_ (H.ClassName "code-review-controls") ]
        [ HH.button
            [ HP.class_ (H.ClassName "refresh-btn theme-button")
            , HE.onClick \_ -> RefreshReview
            , HP.disabled state.loading
            ]
            [ HH.text (if state.loading then "Reviewing..." else "Refresh Review") ]
        , HH.label
            [ HP.class_ (H.ClassName "auto-review-toggle") ]
            [ HH.input
                [ HP.type_ HP.InputCheckbox
                , HP.checked state.autoReview
                , HE.onChecked \checked -> ToggleAutoReview
                ]
            , HH.text "Auto-review on change"
            ]
        ]
    ]

-- | Render quality score
renderQualityScore :: forall m. Maybe CodeReviewResult -> H.ComponentHTML Action () m
renderQualityScore Nothing = HH.text ""
renderQualityScore (Just result) =
  HH.div
    [ HP.class_ (H.ClassName "quality-score") ]
    [ HH.h3
        [ HP.class_ (H.ClassName "score-title") ]
        [ HH.text "Quality Score" ]
    , HH.div
        [ HP.class_ (H.ClassName "score-overall") ]
        [ HH.span
            [ HP.class_ (H.ClassName "score-label") ]
            [ HH.text "Overall: " ]
        , HH.span
            [ HP.class_ (H.ClassName ("score-value " <> scoreClass result.score.overall))
            ]
            [ HH.text (show (Number.floor (result.score.overall * 100.0)) <> "%") ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "score-breakdown") ]
        [ renderScoreItem "Security" result.score.security
        , renderScoreItem "Performance" result.score.performance
        , renderScoreItem "Maintainability" result.score.maintainability
        , renderScoreItem "Test Coverage" result.score.testCoverage
        ]
    ]

-- | Render score item
renderScoreItem :: forall m. String -> Number -> H.ComponentHTML Action () m
renderScoreItem label value =
  HH.div
    [ HP.class_ (H.ClassName "score-item") ]
    [ HH.span
        [ HP.class_ (H.ClassName "score-item-label") ]
        [ HH.text (label <> ": ") ]
    , HH.span
        [ HP.class_ (H.ClassName ("score-item-value " <> scoreClass value))
        ]
        [ HH.text (show (Number.floor (value * 100.0)) <> "%") ]
    ]

-- | Get CSS class for score
scoreClass :: Number -> String
scoreClass score
  | score >= 0.8 = "score-high"
  | score >= 0.6 = "score-medium"
  | score >= 0.4 = "score-low"
  | otherwise = "score-critical"

-- | Render filters
renderFilters :: forall m. State -> H.ComponentHTML Action () m
renderFilters state =
  HH.div
    [ HP.class_ (H.ClassName "code-review-filters") ]
    [ HH.div
        [ HP.class_ (H.ClassName "filter-group") ]
        [ HH.label [] [ HH.text "Severity: " ]
        , HH.select
            [ HP.class_ (H.ClassName "severity-filter")
            , HE.onValueChange \value ->
                SeverityFilterChanged (case value of
                  "critical" -> Just Critical
                  "major" -> Just Major
                  "minor" -> Just Minor
                  "info" -> Just Info
                  _ -> Nothing)
            ]
            [ HH.option [ HP.value "" ] [ HH.text "All" ]
            , HH.option [ HP.value "critical" ] [ HH.text "Critical" ]
            , HH.option [ HP.value "major" ] [ HH.text "Major" ]
            , HH.option [ HP.value "minor" ] [ HH.text "Minor" ]
            , HH.option [ HP.value "info" ] [ HH.text "Info" ]
            ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "filter-group") ]
        [ HH.label [] [ HH.text "Category: " ]
        , HH.select
            [ HP.class_ (H.ClassName "category-filter")
            , HE.onValueChange \value ->
                CategoryFilterChanged (case value of
                  "security" -> Just SecurityIssue
                  "performance" -> Just PerformanceIssue
                  "quality" -> Just QualityIssue
                  "style" -> Just StyleIssue
                  "best-practice" -> Just BestPracticeIssue
                  _ -> Nothing)
            ]
            [ HH.option [ HP.value "" ] [ HH.text "All" ]
            , HH.option [ HP.value "security" ] [ HH.text "Security" ]
            , HH.option [ HP.value "performance" ] [ HH.text "Performance" ]
            , HH.option [ HP.value "quality" ] [ HH.text "Quality" ]
            , HH.option [ HP.value "style" ] [ HH.text "Style" ]
            , HH.option [ HP.value "best-practice" ] [ HH.text "Best Practice" ]
            ]
        ]
    ]

-- | Render issues list
renderIssuesList :: forall m. State -> H.ComponentHTML Action () m
renderIssuesList state =
  case state.currentResult of
    Nothing -> HH.div [ HP.class_ (H.ClassName "no-issues") ] [ HH.text "No review results yet" ]
    Just result -> do
      let filteredIssues = filterIssues result.issues state.filterSeverity state.filterCategory
      HH.div
        [ HP.class_ (H.ClassName "issues-list") ]
        [ HH.div
            [ HP.class_ (H.ClassName "issues-header") ]
            [ HH.text ("Found " <> show (Array.length filteredIssues) <> " issues") ]
        , HH.ul
            [ HP.class_ (H.ClassName "issues") ]
            (Array.mapWithIndex (\index issue ->
              HH.li
                [ HP.class_ (H.ClassName ("issue-item " <> severityClass issue.severity))
                , HE.onClick \_ -> IssueSelected issue
                ]
                [ renderIssueSummary issue ]
            ) filteredIssues)
        ]

-- | Filter issues by severity and category
filterIssues :: Array CodeReviewIssue -> Maybe Severity -> Maybe IssueCategory -> Array CodeReviewIssue
filterIssues issues severityFilter categoryFilter =
  Array.filter (\issue ->
    (case severityFilter of
      Nothing -> true
      Just severity -> issue.severity == severity) &&
    (case categoryFilter of
      Nothing -> true
      Just category -> issue.category == category)
  ) issues

-- | Render issue summary
renderIssueSummary :: forall m. CodeReviewIssue -> H.ComponentHTML Action () m
renderIssueSummary issue =
  HH.div
    [ HP.class_ (H.ClassName "issue-summary") ]
    [ HH.div
        [ HP.class_ (H.ClassName "issue-severity-badge") ]
        [ HH.text (showSeverity issue.severity) ]
    , HH.div
        [ HP.class_ (H.ClassName "issue-category-badge") ]
        [ HH.text (showCategory issue.category) ]
    , HH.div
        [ HP.class_ (H.ClassName "issue-message") ]
        [ HH.text issue.message ]
    , HH.div
        [ HP.class_ (H.ClassName "issue-location") ]
        [ HH.text (issue.location.file <> ":" <> show issue.location.line <> ":" <> show issue.location.column) ]
    ]

-- | Render issue detail
renderIssueDetail :: forall m. Maybe CodeReviewIssue -> H.ComponentHTML Action () m
renderIssueDetail Nothing = HH.text ""
renderIssueDetail (Just issue) =
  HH.div
    [ HP.class_ (H.ClassName "issue-detail") ]
    [ HH.h3
        [ HP.class_ (H.ClassName "issue-detail-title") ]
        [ HH.text issue.message ]
    , HH.div
        [ HP.class_ (H.ClassName "issue-detail-meta") ]
        [ HH.div [] [ HH.text ("Severity: " <> showSeverity issue.severity) ]
        , HH.div [] [ HH.text ("Category: " <> showCategory issue.category) ]
        , HH.div [] [ HH.text ("Rule: " <> issue.rule) ]
        , HH.div [] [ HH.text ("Confidence: " <> show (Number.floor (issue.confidence * 100.0)) <> "%") ]
        , HH.div [] [ HH.text ("Location: " <> issue.location.file <> ":" <> show issue.location.line) ]
        ]
    , case issue.suggestion of
        Nothing -> HH.text ""
        Just suggestion ->
          HH.div
            [ HP.class_ (H.ClassName "issue-suggestion") ]
            [ HH.h4 [] [ HH.text "Suggestion" ]
            , HH.p [] [ HH.text suggestion ]
            ]
    , case issue.fix of
        Nothing -> HH.text ""
        Just fix ->
          HH.div
            [ HP.class_ (H.ClassName "issue-fix") ]
            [ HH.h4 [] [ HH.text "Fix" ]
            , HH.p [] [ HH.text fix.description ]
            , HH.pre
                [ HP.class_ (H.ClassName "fix-code") ]
                [ HH.text fix.replacement ]
            , HH.button
                [ HP.class_ (H.ClassName "apply-fix-btn")
                , HE.onClick \_ -> ApplyFix fix
                , HP.disabled (not fix.autoApplicable)
                ]
                [ HH.text (if fix.autoApplicable then "Apply Fix" else "Fix Not Auto-Applicable") ]
            ]
    ]

-- | Render suggestions
renderSuggestions :: forall m. Maybe CodeReviewResult -> H.ComponentHTML Action () m
renderSuggestions Nothing = HH.text ""
renderSuggestions (Just result) =
  if Array.length result.suggestions == 0 then
    HH.text ""
  else
    HH.div
      [ HP.class_ (H.ClassName "improvement-suggestions") ]
      [ HH.h3 [] [ HH.text "Improvement Suggestions" ]
      , HH.ul
          [ HP.class_ (H.ClassName "suggestions-list") ]
          (Array.map (\suggestion ->
            HH.li
              [ HP.class_ (H.ClassName "suggestion-item") ]
              [ HH.div
                  [ HP.class_ (H.ClassName "suggestion-priority") ]
                  [ HH.text ("Priority: " <> show suggestion.priority) ]
              , HH.div
                  [ HP.class_ (H.ClassName "suggestion-description") ]
                  [ HH.text suggestion.description ]
              , HH.div
                  [ HP.class_ (H.ClassName "suggestion-impact") ]
                  [ HH.text ("Impact: " <> suggestion.impact) ]
              , HH.div
                  [ HP.class_ (H.ClassName "suggestion-effort") ]
                  [ HH.text ("Effort: " <> suggestion.effort) ]
              ]
          ) result.suggestions)
      ]

-- | Show severity as string
showSeverity :: Severity -> String
showSeverity = case _ of
  Critical -> "Critical"
  Major -> "Major"
  Minor -> "Minor"
  Info -> "Info"

-- | Show category as string
showCategory :: IssueCategory -> String
showCategory = case _ of
  SecurityIssue -> "Security"
  PerformanceIssue -> "Performance"
  QualityIssue -> "Quality"
  StyleIssue -> "Style"
  BestPracticeIssue -> "Best Practice"

-- | Get CSS class for severity
severityClass :: Severity -> String
severityClass = case _ of
  Critical -> "severity-critical"
  Major -> "severity-major"
  Minor -> "severity-minor"
  Info -> "severity-info"

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Auto-review if enabled and input provided
    pure unit
  
  ReviewFile filePath content -> do
    H.modify_ _ { loading = true }
    result <- H.lift $ reviewCode filePath content
    H.modify_ _ { currentResult = Just result, loading = false }
    H.raise (ReviewCompleted result)
  
  IssueSelected issue -> do
    H.modify_ _ { selectedIssue = Just issue }
  
  SeverityFilterChanged severity -> do
    H.modify_ _ { filterSeverity = severity }
  
  CategoryFilterChanged category -> do
    H.modify_ _ { filterCategory = category }
  
  ApplyFix fix -> do
    H.raise (FixApplied fix)
  
  DismissIssue issue -> do
    H.modify_ \s -> s
      { currentResult = case s.currentResult of
          Nothing -> Nothing
          Just result -> Just result
            { issues = Array.filter (\i -> i /= issue) result.issues
            }
      }
    H.raise (IssueDismissed issue)
  
  ToggleAutoReview -> do
    H.modify_ \s -> s { autoReview = not s.autoReview }
  
  RefreshReview -> do
    state <- H.get
    case state.currentResult of
      Nothing -> pure unit
      Just result -> do
        handleAction (ReviewFile result.file "")
  
-- | Import Data.Number
import Data.Number as Number
