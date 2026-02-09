-- | Agent Output Viewer Components
-- | Individual components for rendering agent output sections
module Nexus.AgentOutputViewer.Components where

import Prelude

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Nexus.AgentOutputViewer.Types
  ( OutputStatus(..)
  , EvidenceType(..)
  , FileChange
  , Violation
  , ViolationSeverity(..)
  , NextStep
  , StepPriority(..)
  , ChecklistItem
  )

-- | Render status header with icon and summary
renderStatusHeader :: forall m action. OutputStatus -> String -> H.ComponentHTML action () m
renderStatusHeader status summary =
  HH.div
    [ HP.class_ (HH.ClassName "status-header") ]
    [ HH.div
        [ HP.class_ (HH.ClassName ("status-" <> statusClass status)) ]
        [ HH.text (statusIcon status <> " STATUS: " <> statusText status) ]
    , HH.p
        [ HP.class_ (HH.ClassName "summary") ]
        [ HH.text summary ]
    ]
  where
    statusClass Success = "success"
    statusClass Failure = "failure"
    statusClass Partial = "partial"
    statusClass InProgress = "in-progress"
    
    statusIcon Success = "[SUCCESS]"
    statusIcon Failure = "[FAILURE]"
    statusIcon Partial = "[PARTIAL]"
    statusIcon InProgress = "[IN_PROGRESS]"
    
    statusText Success = "SUCCESS"
    statusText Failure = "FAILURE"
    statusText Partial = "PARTIAL"
    statusText InProgress = "IN_PROGRESS"

-- | Render evidence section with classification
renderEvidenceSection :: forall m action. Maybe (Array EvidenceType) -> H.ComponentHTML action () m
renderEvidenceSection Nothing = HH.text ""
renderEvidenceSection (Just evidence) =
  HH.div
    [ HP.class_ (HH.ClassName "evidence-section") ]
    [ HH.h3_ [ HH.text "Evidence" ]
    , HH.ul
        [ HP.class_ (HH.ClassName "evidence-list") ]
        (Array.map renderEvidenceItem evidence)
    ]

renderEvidenceItem :: forall m action. EvidenceType -> H.ComponentHTML action () m
renderEvidenceItem = case _ of
  Verified fileLine desc ->
    HH.li
      [ HP.class_ (HH.ClassName "evidence-verified") ]
      [ HH.span
          [ HP.class_ (HH.ClassName "evidence-label") ]
          [ HH.text "Verified" ]
      , HH.text (" — " <> fileLine <> " " <> desc)
      ]
  Assumed reasoning desc ->
    HH.li
      [ HP.class_ (HH.ClassName "evidence-assumed") ]
      [ HH.span
          [ HP.class_ (HH.ClassName "evidence-label") ]
          [ HH.text "Assumed" ]
      , HH.text (" — " <> reasoning <> " " <> desc)
      ]
  NeedsVerification what how ->
    HH.li
      [ HP.class_ (HH.ClassName "evidence-needs-verification") ]
      [ HH.span
          [ HP.class_ (HH.ClassName "evidence-label") ]
          [ HH.text "Needs Verification" ]
      , HH.text (" — " <> what <> " Verify by: " <> how)
      ]

-- | Render changes section with files table
renderChangesSection :: forall m action. Maybe (Array FileChange) -> H.ComponentHTML action () m
renderChangesSection Nothing = HH.text ""
renderChangesSection (Just changes) =
  HH.div
    [ HP.class_ (HH.ClassName "changes-section") ]
    [ HH.h3_ [ HH.text "What Changed" ]
    , renderFilesTable changes
    ]

renderFilesTable :: forall m action. Array FileChange -> H.ComponentHTML action () m
renderFilesTable changes =
  HH.table
    [ HP.class_ (HH.ClassName "files-table") ]
    [ HH.thead_
        [ HH.tr_
            [ HH.th_ [ HH.text "File" ]
            , HH.th_ [ HH.text "Lines Changed" ]
            , HH.th_ [ HH.text "Type" ]
            ]
        ]
    , HH.tbody_
        (Array.map renderFileRow changes)
    ]

renderFileRow :: forall m action. FileChange -> H.ComponentHTML action () m
renderFileRow change =
  HH.tr_
    [ HH.td_ [ HH.text change.file ]
    , HH.td_ [ HH.text change.lines ]
    , HH.td_ [ HH.text change.changeType ]
    ]

-- | Render violations section with summary table
renderViolationsSection :: forall m action. Maybe (Array Violation) -> (String -> action) -> H.ComponentHTML action () m
renderViolationsSection Nothing _ = HH.text ""
renderViolationsSection (Just violations) copyAction =
  HH.div
    [ HP.class_ (HH.ClassName "violations-section") ]
    [ HH.h3_ [ HH.text "Violations Summary" ]
    , renderViolationsSummary violations
    , HH.div
        [ HP.class_ (HH.ClassName "violations-list") ]
        (Array.map (renderViolation copyAction) violations)
    ]

renderViolationsSummary :: forall m action. Array Violation -> H.ComponentHTML action () m
renderViolationsSummary violations =
  let
    critical = Array.filter (\v -> v.severity == Critical) violations
    high = Array.filter (\v -> v.severity == High) violations
    medium = Array.filter (\v -> v.severity == Medium) violations
    low = Array.filter (\v -> v.severity == Low) violations
  in
    HH.table
      [ HP.class_ (HH.ClassName "violations-summary") ]
      [ HH.thead_
          [ HH.tr_
              [ HH.th_ [ HH.text "Severity" ]
              , HH.th_ [ HH.text "Count" ]
              , HH.th_ [ HH.text "Status" ]
              ]
          ]
      , HH.tbody_
          [ renderSummaryRow "CRITICAL" (Array.length critical) "BLOCKED"
          , renderSummaryRow "HIGH" (Array.length high) "REQUIRES FIX"
          , renderSummaryRow "MEDIUM" (Array.length medium) "WARNING"
          , renderSummaryRow "LOW" (Array.length low) "INFO"
          ]
      ]

renderSummaryRow :: forall m action. String -> Int -> String -> H.ComponentHTML action () m
renderSummaryRow severity count status =
  HH.tr_
    [ HH.td_ [ HH.text severity ]
    , HH.td_ [ HH.text (show count) ]
    , HH.td_ [ HH.text status ]
    ]

renderViolation :: forall m action. (String -> action) -> Violation -> H.ComponentHTML action () m
renderViolation copyAction violation =
  HH.div
    [ HP.class_ (HH.ClassName ("violation-" <> severityClass violation.severity)) ]
    [ HH.h4_ [ HH.text ("Violation #" <> violation.id <> ": " <> violation.violation) ]
    , HH.p_ [ HH.text ("Location: " <> violation.location) ]
    , HH.p_ [ HH.text ("Impact: " <> violation.impact) ]
    , HH.p_ [ HH.text ("Remediation: " <> violation.remediation) ]
    , case violation.fixCode of
        Just code ->
          HH.pre
            [ HP.class_ (HH.ClassName "fix-code") ]
            [ HH.code_ [ HH.text code ] ]
        Nothing -> HH.text ""
    , case violation.verification of
        Just cmd ->
          HH.div
            [ HP.class_ (HH.ClassName "verification-command") ]
            [ HH.code_ [ HH.text cmd ]
            , HH.button
                [ HP.class_ (HH.ClassName "copy-button")
                , HE.onClick \_ -> copyAction cmd
                ]
                [ HH.text "Copy" ]
            ]
        Nothing -> HH.text ""
    ]
  where
    severityClass Critical = "critical"
    severityClass High = "high"
    severityClass Medium = "medium"
    severityClass Low = "low"

-- | Render next steps section
renderNextStepsSection :: forall m action. Maybe (Array NextStep) -> H.ComponentHTML action () m
renderNextStepsSection Nothing = HH.text ""
renderNextStepsSection (Just steps) =
  HH.div
    [ HP.class_ (HH.ClassName "next-steps-section") ]
    [ HH.h3_ [ HH.text "Next Steps" ]
    , HH.ol
        [ HP.class_ (HH.ClassName "next-steps-list") ]
        (Array.mapWithIndex renderNextStep steps)
    ]

renderNextStep :: forall m action. Int -> NextStep -> H.ComponentHTML action () m
renderNextStep idx step =
  HH.li_
    [ HH.span
        [ HP.class_ (HH.ClassName ("priority-" <> priorityClass step.priority)) ]
        [ HH.text (priorityIcon step.priority <> " " <> show (idx + 1) <> ". " <> step.step) ]
    , case step.details of
        Just details ->
          HH.div
            [ HP.class_ (HH.ClassName "step-details") ]
            [ HH.text details ]
        Nothing -> HH.text ""
    ]

priorityIcon :: StepPriority -> String
priorityIcon StepHigh = "[HIGH]"
priorityIcon StepMedium = "[MEDIUM]"
priorityIcon StepLow = "[LOW]"

priorityClass :: StepPriority -> String
priorityClass StepHigh = "high"
priorityClass StepMedium = "medium"
priorityClass StepLow = "low"

-- | Render verification section with copy buttons
renderVerificationSection :: forall m action. Maybe (Array String) -> (String -> action) -> H.ComponentHTML action () m
renderVerificationSection Nothing _ = HH.text ""
renderVerificationSection (Just commands) copyAction =
  HH.div
    [ HP.class_ (HH.ClassName "verification-section") ]
    [ HH.h3_ [ HH.text "Verification" ]
    , HH.div
        [ HP.class_ (HH.ClassName "commands-list") ]
        (Array.map (renderCommand copyAction) commands)
    ]

renderCommand :: forall m action. (String -> action) -> String -> H.ComponentHTML action () m
renderCommand copyAction cmd =
  HH.div
    [ HP.class_ (HH.ClassName "command") ]
    [ HH.pre
        [ HP.class_ (HH.ClassName "command-code") ]
        [ HH.code_ [ HH.text ("$ " <> cmd) ] ]
    , HH.button
        [ HP.class_ (HH.ClassName "copy-button")
        , HE.onClick \_ -> copyAction cmd
        ]
        [ HH.text "Copy" ]
    ]

-- | Render completion checklist
renderCompletionChecklist :: forall m action. Maybe (Array ChecklistItem) -> H.ComponentHTML action () m
renderCompletionChecklist Nothing = HH.text ""
renderCompletionChecklist (Just items) =
  HH.div
    [ HP.class_ (HH.ClassName "completion-checklist") ]
    [ HH.h3_ [ HH.text "Completion Checklist" ]
    , HH.ul
        [ HP.class_ (HH.ClassName "checklist-items") ]
        (Array.mapWithIndex renderChecklistItem items)
    ]

renderChecklistItem :: forall m action. Int -> ChecklistItem -> H.ComponentHTML action () m
renderChecklistItem idx item =
  HH.li_
    [ HH.label_
        [ HH.input
            [ HP.type_ HP.InputCheckbox
            , HP.checked item.checked
            , HP.disabled item.inProgress
            ]
        , HH.text item.label
        , if item.inProgress then
            HH.span
              [ HP.class_ (HH.ClassName "in-progress") ]
              [ HH.text " (in progress...)" ]
          else
            HH.text ""
        ]
    ]
