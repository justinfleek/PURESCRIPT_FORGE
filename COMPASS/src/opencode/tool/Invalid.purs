{-|
Module      : Tool.Invalid
Description : Handler for invalid tool calls
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Invalid Tool

This is a special tool that handles cases where the AI model
attempts to call a tool with invalid arguments. It provides
clear error messages to help the model correct its call.

== Coeffect Equation

@
  invalid : InvalidParams -> Graded Unit ToolResult

  -- No resources required (error reporting only)
@

== Use Cases

1. Schema validation failures
2. Missing required parameters
3. Type mismatches in arguments
4. Unknown tool names

== Error Format

The output clearly explains:
- What tool was called
- What error occurred
- How to fix the issue
-}
module Tool.Invalid
  ( -- * Tool Interface
    InvalidParams(..)
  , execute
  , invalidTool
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Argonaut (Json, class EncodeJson, encodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Parameters for invalid tool.

@
  record InvalidParams where
    tool  : String   -- Name of the tool that was called
    error : String   -- Description of what went wrong
@
-}
type InvalidParams =
  { tool :: String
  , error :: String
  }

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

{-| Execute invalid tool.

Returns an error message explaining what went wrong with the tool call.
-}
execute :: InvalidParams -> ToolContext -> Aff ToolResult
execute params _ctx = pure
  { title: "Invalid Tool"
  , metadata: encodeJson
      { tool: params.tool
      , error: params.error
      }
  , output: "The arguments provided to the tool are invalid: " <> params.error
  , attachments: Nothing
  }

{-| Tool registration.

Note: This tool should NOT be listed in available tools.
It is used internally when other tool calls fail validation.
-}
invalidTool :: ToolInfo
invalidTool =
  { id: "invalid"
  , description: "Do not use"  -- Hidden from model
  , parameters: encodeJson invalidSchema
  , execute: \json ctx ->
      -- Parse params or use defaults
      let params = { tool: "unknown", error: "Unknown error" }
      in execute params ctx
  , formatValidationError: Nothing
  }

-- ============================================================================
-- HELPERS
-- ============================================================================

invalidSchema :: { type :: String }
invalidSchema = { type: "object" }
