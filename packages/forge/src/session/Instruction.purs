{-|
Module      : Forge.Session.Instruction
Description : Session Instructions

Manages system instructions that guide agent behavior.
Instructions can come from system defaults, project configuration,
or user settings.

== Instruction Sources

| Source  | Priority | Description                    |
|---------|----------|--------------------------------|
| system  | 0        | Core system instructions       |
| project | 10       | Project-specific (.forge/)     |
| user    | 20       | User preferences               |
| session | 30       | Session-specific overrides     |

Higher priority instructions override lower ones.
-}
module Forge.Session.Instruction
  ( -- * Types
    Instruction
  , InstructionSource(..)
  , InstructionSet
    -- * Instruction Operations
  , getInstructions
  , addInstruction
  , removeInstruction
  , updateInstruction
    -- * Instruction Queries
  , getBySource
  , getEffective
  , merge
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Instruction source
data InstructionSource
  = SystemSource
  | ProjectSource
  | UserSource
  | SessionSource

derive instance eqInstructionSource :: Eq InstructionSource
derive instance ordInstructionSource :: Ord InstructionSource

instance showInstructionSource :: Show InstructionSource where
  show SystemSource = "system"
  show ProjectSource = "project"
  show UserSource = "user"
  show SessionSource = "session"

-- | Single instruction
type Instruction =
  { id :: String
  , content :: String
  , priority :: Int
  , source :: InstructionSource
  , enabled :: Boolean
  , tags :: Array String
  }

-- | Set of instructions
type InstructionSet =
  { instructions :: Array Instruction
  , merged :: String  -- Combined effective instruction
  }

-- ============================================================================
-- FFI
-- ============================================================================

foreign import loadInstructionsFFI :: String -> Aff (Array Instruction)
foreign import saveInstructionFFI :: String -> Instruction -> Aff (Either String Unit)
foreign import deleteInstructionFFI :: String -> String -> Aff (Either String Unit)
foreign import generateIdFFI :: Aff String

-- ============================================================================
-- INSTRUCTION OPERATIONS
-- ============================================================================

{-| Get all active instructions for a session.

Returns instructions from all sources, sorted by priority.
-}
getInstructions :: String -> Aff (Either String (Array Instruction))
getInstructions sessionId = do
  instructions <- loadInstructionsFFI sessionId
  let sorted = Array.sortBy comparePriority instructions
  let enabled = Array.filter _.enabled sorted
  pure $ Right enabled

{-| Add an instruction to the session. -}
addInstruction :: String -> Instruction -> Aff (Either String Unit)
addInstruction sessionId instruction = do
  -- Ensure instruction has an ID
  instWithId <- case instruction.id of
    "" -> do
      newId <- generateIdFFI
      pure instruction { id = newId }
    _ -> pure instruction
  
  saveInstructionFFI sessionId instWithId

{-| Remove an instruction. -}
removeInstruction :: String -> String -> Aff (Either String Unit)
removeInstruction = deleteInstructionFFI

{-| Update an existing instruction. -}
updateInstruction :: String -> Instruction -> Aff (Either String Unit)
updateInstruction = saveInstructionFFI

-- ============================================================================
-- INSTRUCTION QUERIES
-- ============================================================================

{-| Get instructions from a specific source. -}
getBySource :: String -> InstructionSource -> Aff (Array Instruction)
getBySource sessionId source = do
  result <- getInstructions sessionId
  case result of
    Left _ -> pure []
    Right instructions -> pure $ Array.filter (\i -> i.source == source) instructions

{-| Get the effective (merged) instruction set.

Combines all enabled instructions into a single instruction set.
-}
getEffective :: String -> Aff (Either String InstructionSet)
getEffective sessionId = do
  result <- getInstructions sessionId
  case result of
    Left err -> pure $ Left err
    Right instructions ->
      let merged = mergeInstructions instructions
      in pure $ Right { instructions, merged }

{-| Merge multiple instructions into one. -}
merge :: Array Instruction -> String
merge = mergeInstructions

-- ============================================================================
-- HELPERS
-- ============================================================================

comparePriority :: Instruction -> Instruction -> Ordering
comparePriority a b = compare a.priority b.priority

mergeInstructions :: Array Instruction -> String
mergeInstructions instructions =
  instructions
    # Array.filter _.enabled
    # Array.sortBy comparePriority
    # map formatInstruction
    # String.joinWith "\n\n"

formatInstruction :: Instruction -> String
formatInstruction inst =
  "## " <> show inst.source <> " instruction\n" <> inst.content

sourceToPriority :: InstructionSource -> Int
sourceToPriority SystemSource = 0
sourceToPriority ProjectSource = 10
sourceToPriority UserSource = 20
sourceToPriority SessionSource = 30
