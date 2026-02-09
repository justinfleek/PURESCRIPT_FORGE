-- | Agent Output Viewer Types
-- | Type definitions for structured agent outputs
module Nexus.AgentOutputViewer.Types where

import Prelude

-- | Agent output status
data OutputStatus
  = Success
  | Failure
  | Partial
  | InProgress

derive instance Eq OutputStatus
derive instance Ord OutputStatus

-- | Evidence classification
data EvidenceType
  = Verified String String  -- file:line, description
  | Assumed String String   -- reasoning, what needs verification
  | NeedsVerification String String  -- what is unknown, how to verify

derive instance Eq EvidenceType

-- | File change record
type FileChange =
  { file :: String
  , lines :: String
  , changeType :: String
  }

-- | Violation severity
data ViolationSeverity
  = Critical
  | High
  | Medium
  | Low

derive instance Eq ViolationSeverity
derive instance Ord ViolationSeverity

-- | Violation record
type Violation =
  { id :: String
  , severity :: ViolationSeverity
  , location :: String  -- file:line
  , violation :: String
  , impact :: String
  , remediation :: String
  , fixCode :: Maybe String
  , verification :: Maybe String
  }

-- | Next step priority
data StepPriority
  = StepHigh
  | StepMedium
  | StepLow

derive instance Eq StepPriority
derive instance Ord StepPriority

-- | Next step record
type NextStep =
  { priority :: StepPriority
  , step :: String
  , details :: Maybe String
  }

-- | Checklist item
type ChecklistItem =
  { label :: String
  , checked :: Boolean
  , inProgress :: Boolean
  }

-- | Agent output structure (matches Output Format Protocol)
type AgentOutput =
  { status :: OutputStatus
  , summary :: String
  , whatChanged :: Maybe (Array FileChange)
  , evidence :: Maybe (Array EvidenceType)
  , violations :: Maybe (Array Violation)
  , nextSteps :: Maybe (Array NextStep)
  , verification :: Maybe (Array String)  -- commands
  , details :: Maybe String  -- markdown
  , completionChecklist :: Maybe (Array ChecklistItem)
  }
