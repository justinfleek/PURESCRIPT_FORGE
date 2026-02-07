{-|
Module      : Forge.Tool.Plan
Description : Plan mode transition tools
= Plan Tool

This module provides tools for transitioning between plan and build modes.
The plan mode is for research and planning, while build mode is for
implementing changes.

== Coeffect Equation

@
  planExit  : Unit -> Graded (Session * UI) ToolResult
  planEnter : Unit -> Graded (Session * UI) ToolResult

  -- Requires:
  -- 1. Session access for agent switching
  -- 2. UI access for user confirmation
@

== Agent Modes

| Mode  | Description                    | Capabilities           |
|-------|--------------------------------|------------------------|
| plan  | Research and planning          | Read-only, can't edit  |
| build | Implementation                 | Full file editing      |

== Plan File

The plan is stored as a markdown file in the project:
@
  .opencode/plan.md
@

This file persists across sessions and can be version controlled.
-}
module Forge.Tool.Plan
  ( -- * Tool Interface
    PlanExitParams
  , PlanEnterParams
  , executePlanExit
  , executePlanEnter
  , planExitTool
  , planEnterTool
    -- * Plan Types
  , AgentMode(..)
  , PlanFile
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Argonaut (Json, encodeJson)
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Tool result type
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Json
  , attachments :: Maybe (Array Json)
  }

-- | Tool context
type ToolContext = 
  { workspaceRoot :: String
  }

-- | Tool info
type ToolInfo =
  { id :: String
  , description :: String
  , parameters :: Json
  , execute :: Json -> ToolContext -> Aff ToolResult
  , formatValidationError :: Maybe (Json -> String)
  }

{-| Agent mode for session. -}
data AgentMode
  = PlanMode   -- Research and planning (read-only)
  | BuildMode  -- Implementation (full editing)

derive instance eqAgentMode :: Eq AgentMode

instance showAgentMode :: Show AgentMode where
  show PlanMode = "plan"
  show BuildMode = "build"

{-| Plan file info. -}
type PlanFile =
  { path :: String       -- Relative path to plan file
  , absolutePath :: String
  , exists :: Boolean
  }

{-| Parameters for plan_exit tool (empty). -}
type PlanExitParams = {}

{-| Parameters for plan_enter tool (empty). -}
type PlanEnterParams = {}

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

{-| Execute plan_exit tool.

Asks user to confirm switching from plan mode to build mode.
Creates a synthetic user message to trigger the agent switch.
-}
executePlanExit :: PlanExitParams -> ToolContext -> Aff ToolResult
executePlanExit _ ctx = do
  -- 1. Get session and plan file path
  -- 2. Ask user for confirmation
  -- 3. If confirmed, create message to switch to build agent
  -- 4. Return result
  
  let planPath = ctx.workspaceRoot <> "/.opencode/plan.md"
  
  -- Ask user for confirmation using Question tool pattern
  -- In production, this would use the Question tool or UI bridge
  -- For now, format the confirmation request
  let confirmationMessage = 
        "Switch from plan mode to build mode?\n\n" <>
        "Plan mode: Research and planning (read-only)\n" <>
        "Build mode: Full implementation (can edit files)\n\n" <>
        "Plan file: " <> planPath <> "\n\n" <>
        "User confirmation required. In production, this would prompt via UI."
  
  pure
    { title: "Switching to build agent"
    , metadata: encodeJson { agent: "build", plan: planPath }
    , output: confirmationMessage
    , attachments: Nothing
    }

{-| Execute plan_enter tool.

Asks user to confirm switching from build mode to plan mode.
Creates a synthetic user message to trigger the agent switch.
-}
executePlanEnter :: PlanEnterParams -> ToolContext -> Aff ToolResult
executePlanEnter _ ctx = do
  -- 1. Get session and plan file path
  -- 2. Ask user for confirmation
  -- 3. If confirmed, create message to switch to plan agent
  -- 4. Return result
  
  let planPath = ctx.workspaceRoot <> "/.opencode/plan.md"
  
  -- Ask user for confirmation using Question tool pattern
  -- In production, this would use the Question tool or UI bridge
  -- For now, format the confirmation request
  let confirmationMessage =
        "Switch from build mode to plan mode?\n\n" <>
        "Build mode: Full implementation (can edit files)\n" <>
        "Plan mode: Research and planning (read-only)\n\n" <>
        "Plan file: " <> planPath <> "\n\n" <>
        "User confirmation required. In production, this would prompt via UI."
  
  pure
    { title: "Switching to plan agent"
    , metadata: encodeJson { agent: "plan", plan: planPath }
    , output: confirmationMessage
    , attachments: Nothing
    }

{-| PlanExit tool registration. -}
planExitTool :: ToolInfo
planExitTool =
  { id: "plan_exit"
  , description: planExitDescription
  , parameters: emptySchema
  , execute: \_ ctx -> executePlanExit {} ctx
  , formatValidationError: Nothing
  }

{-| PlanEnter tool registration. -}
planEnterTool :: ToolInfo
planEnterTool =
  { id: "plan_enter"
  , description: planEnterDescription
  , parameters: emptySchema
  , execute: \_ ctx -> executePlanEnter {} ctx
  , formatValidationError: Nothing
  }

-- ============================================================================
-- DESCRIPTIONS
-- ============================================================================

planExitDescription :: String
planExitDescription = 
  "Use this tool when you've finished creating the plan and want to " <>
  "switch to the build agent to start implementing."

planEnterDescription :: String
planEnterDescription =
  "Use this tool when you want to switch to the plan agent for " <>
  "research and planning instead of making changes."

emptySchema :: Json
emptySchema = encodeJson { "type": "object" }
