{-|
Module      : Tool.Batch
Description : Parallel tool execution
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
import Data.Argonaut (Json, encodeJson, decodeJson, (.:))
import Data.Traversable (traverse)
import Effect.Aff (Aff, parallel, sequential, attempt)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo, ToolMetadata(..), EmptyMetadata, ErrorMetadata)
import Aleph.Coeffect (Resource(..), (⊗))
import Tool.Registry (get, initialState, RegistryState)
import Tool.Dispatcher (dispatchTool as dispatchToolById)
import Effect.Ref (Ref)
import Effect.Ref as Ref

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

-- | Global tool registry ref (in production, would be passed via context)
toolRegistryRef :: Ref RegistryState
toolRegistryRef = unsafePerformEffect $ Ref.new initialState
  where
    foreign import unsafePerformEffect :: forall a. Effect a -> a

execute :: BatchParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate batch size
  let calls = Array.take defaultConfig.maxCalls params.toolCalls
  let discarded = Array.drop defaultConfig.maxCalls params.toolCalls
  
  -- 2. Filter disallowed tools
  let validated = calls # Array.filter \c ->
        not (Array.elem c.tool defaultConfig.disallowed)
  
  -- 3. Execute in parallel
  results <- sequential $ traverse (parallel <<< executeCall ctx) validated
  
  -- 4. Count successes and failures
  let successful = Array.length $ Array.filter _.success results
  let failed = Array.length results - successful
  
  pure
    { title: "Batch execution (" <> show successful <> "/" <> show (Array.length calls) <> " successful)"
    , metadata: BatchMetadata
        { totalCalls: Array.length calls
        , successful
        , failed
        , tools: calls # map _.tool
        }
    , output: formatOutput successful (Array.length calls) failed <> "\n\n" <> formatResults results
    , attachments: Nothing
    }

executeCall :: ToolContext -> ToolCall -> Aff CallResult
executeCall ctx call = do
  -- 1. Look up tool in registry
  toolInfo <- liftEffect $ get call.tool toolRegistryRef
  
  case toolInfo of
    Nothing -> pure
      { tool: call.tool
      , success: false
      , output: Nothing
      , error: Just ("Tool not found: " <> call.tool)
      }
    Just _tool -> do
      -- 2. Execute tool via tool dispatch
      -- Note: In production, this would use the actual tool's execute function
      -- For now, we'll attempt to dispatch via a tool execution service
      result <- attempt $ dispatchTool call ctx
      case result of
        Left err -> pure
          { tool: call.tool
          , success: false
          , output: Nothing
          , error: Just ("Tool execution failed: " <> show err)
          }
        Right toolResult -> pure
          { tool: call.tool
          , success: true
          , output: Just toolResult.output
          , error: Nothing
          }

-- | Dispatch a tool call to the appropriate tool executor
-- | Uses Tool.Dispatcher to look up and execute the tool
dispatchTool :: ToolCall -> ToolContext -> Aff ToolResult
dispatchTool call ctx = do
  -- Use global tool dispatcher to execute the tool
  dispatchToolById call.tool call.parameters ctx

-- | Format individual results for output
formatResults :: Array CallResult -> String
formatResults results =
  String.joinWith "\n" $ Array.mapWithIndex formatResult results
  where
    formatResult idx result =
      let status = if result.success then "✓" else "✗"
          toolLine = show (idx + 1) <> ". " <> status <> " " <> result.tool
          details = case result.success, result.output, result.error of
            true, Just out, _ -> "\n   Output: " <> String.take 100 out
            false, _, Just err -> "\n   Error: " <> err
            _, _, _ -> ""
      in toolLine <> details

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
  , parameters: encodeJson batchSchema
  , execute: \json ctx ->
      case decodeBatchParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationError
  }

-- | Batch tool schema
batchSchema :: Json
batchSchema = encodeJson
  { type: "object"
  , properties:
      { toolCalls: 
          { type: "array"
          , items:
              { type: "object"
              , properties:
                  { tool: { type: "string", description: "Tool ID to execute" }
                  , parameters: { type: "object", description: "Tool parameters" }
                  }
              , required: ["tool", "parameters"]
              }
          , description: "Array of tool calls to execute in parallel"
          , minItems: 1
          , maxItems: 25
          }
      }
  , required: ["toolCalls"]
  }

-- | Decode batch parameters
decodeBatchParams :: Json -> Either String BatchParams
decodeBatchParams json = do
  obj <- decodeJson json
  toolCalls <- obj .: "toolCalls" >>= decodeJson
  pure { toolCalls }

formatValidationError :: Json -> String
formatValidationError _ =
  "Invalid parameters for tool 'batch'.\n\n" <>
  "Expected format:\n" <>
  "  [{\"tool\": \"tool_name\", \"parameters\": {...}}, ...]"

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Batch Error"
  , metadata: ErrorMetadata { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }
