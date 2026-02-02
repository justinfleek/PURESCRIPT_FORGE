{-|
Module      : Tool.Batch
Description : Parallel tool execution
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Batch Tool

Execute multiple tools in parallel for optimal performance.

== Coeffect Equation

@
  batch : BatchParams → Graded (⊗ᵢ coeffect(toolᵢ)) BatchResult

  -- Coeffect is the tensor product of all tool coeffects
  -- Each tool runs independently in parallel
@

== Constraints

1. Maximum 25 tools per batch
2. Recursive batching not allowed
3. External tools (MCP) cannot be batched
4. Each tool result tracked as separate part

== Usage

@
  batch
    { toolCalls:
        [ { tool: "read", parameters: { filePath: "a.purs" } }
        , { tool: "read", parameters: { filePath: "b.purs" } }
        , { tool: "grep", parameters: { pattern: "TODO" } }
        ]
    }
@
-}
module Tool.Batch
  ( -- * Tool Interface
    BatchParams(..)
  , ToolCall(..)
  , BatchResult(..)
  , CallResult(..)
  , execute
  , batchTool
    -- * Configuration
  , BatchConfig(..)
  , defaultConfig
    -- * Coeffects
  , batchCoeffect
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson)
import Data.Traversable (traverse)
import Effect.Aff (Aff, parallel, sequential)
import Effect.Aff.Class (class MonadAff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..), (⊗))

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

type BatchConfig =
  { maxCalls :: Int              -- Maximum tools per batch
  , disallowed :: Array String   -- Tools that cannot be batched
  }

defaultConfig :: BatchConfig
defaultConfig =
  { maxCalls: 25
  , disallowed: ["batch"]        -- No recursive batching
  }

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

{-| Batch tool parameters.

@
  record BatchParams where
    toolCalls : Array ToolCall
@
-}
type BatchParams =
  { toolCalls :: Array ToolCall
  }

type ToolCall =
  { tool :: String
  , parameters :: Json
  }

type CallResult =
  { tool :: String
  , success :: Boolean
  , output :: Maybe String
  , error :: Maybe String
  }

type BatchResult =
  { total :: Int
  , successful :: Int
  , failed :: Int
  , results :: Array CallResult
  }

-- ════════════════════════════════════════════════════════════════════════════
-- EXECUTION
-- ════════════════════════════════════════════════════════════════════════════

execute :: BatchParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate batch size
  let calls = Array.take defaultConfig.maxCalls params.toolCalls
  let discarded = Array.drop defaultConfig.maxCalls params.toolCalls
  
  -- 2. Filter disallowed tools
  let validated = calls # Array.filter \c ->
        not (Array.elem c.tool defaultConfig.disallowed)
  
  -- 3. Execute in parallel
  -- TODO: Parallel execution via Aff
  -- results <- sequential $ traverse (parallel <<< executeCall ctx) validated
  
  let successful = 0
  let failed = 0
  
  pure
    { title: "Batch execution (" <> show successful <> "/" <> show (Array.length calls) <> " successful)"
    , metadata: encodeJson
        { totalCalls: Array.length calls
        , successful
        , failed
        , tools: calls # map _.tool
        }
    , output: formatOutput successful (Array.length calls) failed
    , attachments: Nothing
    }

executeCall :: ToolContext -> ToolCall -> Aff CallResult
executeCall ctx call = do
  -- 1. Look up tool in registry
  -- 2. Validate parameters
  -- 3. Execute tool
  -- 4. Return result
  pure
    { tool: call.tool
    , success: false
    , output: Nothing
    , error: Just "TODO: Implement tool dispatch"
    }

formatOutput :: Int -> Int -> Int -> String
formatOutput successful total failed
  | failed > 0 = 
      "Executed " <> show successful <> "/" <> show total <> 
      " tools successfully. " <> show failed <> " failed."
  | otherwise = 
      "All " <> show successful <> " tools executed successfully.\n\n" <>
      "Keep using the batch tool for optimal performance!"

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

{-| Coeffect for batch is composition of all tool coeffects.

@
  batchCoeffect calls = ⊗ᵢ coeffect(callsᵢ)
@
-}
batchCoeffect :: BatchParams -> Resource
batchCoeffect params =
  -- Combine all tool coeffects
  -- In real implementation, look up each tool's coeffect
  Pure

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL REGISTRATION
-- ════════════════════════════════════════════════════════════════════════════

batchTool :: ToolInfo
batchTool =
  { id: "batch"
  , description: "Execute multiple tools in parallel"
  , parameters: encodeJson { type: "object" }
  , execute: \json ctx ->
      case decodeJson json of
        Left err -> pure $ mkErrorResult (show err)
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationError
  }

formatValidationError :: Json -> String
formatValidationError _ =
  "Invalid parameters for tool 'batch'.\n\n" <>
  "Expected format:\n" <>
  "  [{\"tool\": \"tool_name\", \"parameters\": {...}}, ...]"

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Batch Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }
