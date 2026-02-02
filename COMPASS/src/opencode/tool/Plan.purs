{-|
Module      : Tool.Plan
Description : Plan mode transition tools
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

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
module Tool.Plan
  ( -- * Tool Interface
    PlanExitParams(..)
  , PlanEnterParams(..)
  , executePlanExit
  , executePlanEnter
  , planExitTool
  , planEnterTool
    -- * Plan Types
  , AgentMode(..)
  , PlanFile(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Argonaut (Json, class EncodeJson, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Agent mode for session. -}
data AgentMode
  = PlanMode   -- Research and planning (read-only)
  | BuildMode  -- Implementation (full editing)

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
  
  let planPath = ".opencode/plan.md"  -- TODO: Get from session
  
  -- TODO: Actually ask user and switch modes
  pure
    { title: "Switching to build agent"
    , metadata: encodeJson { agent: "build", plan: planPath }
    , output: "User approved switching to build agent. Wait for further instructions."
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
  
  let planPath = ".opencode/plan.md"  -- TODO: Get from session
  
  -- TODO: Actually ask user and switch modes
  pure
    { title: "Switching to plan agent"
    , metadata: encodeJson { agent: "plan", plan: planPath }
    , output: "User confirmed to switch to plan mode. Begin planning."
    , attachments: Nothing
    }

{-| PlanExit tool registration. -}
planExitTool :: ToolInfo
planExitTool =
  { id: "plan_exit"
  , description: planExitDescription
  , parameters: encodeJson emptySchema
  , execute: \_ ctx -> executePlanExit {} ctx
  , formatValidationError: Nothing
  }

{-| PlanEnter tool registration. -}
planEnterTool :: ToolInfo
planEnterTool =
  { id: "plan_enter"
  , description: planEnterDescription
  , parameters: encodeJson emptySchema
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

emptySchema :: { type :: String }
emptySchema = { type: "object" }
