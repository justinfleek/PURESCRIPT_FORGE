{-|
Module      : Tool.Skill
Description : Skill loading and management tool
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Skill Tool

This tool loads skills which provide detailed instructions for specific
tasks. Skills are markdown files that contain specialized knowledge and
step-by-step guidance.

== Coeffect Equation

@
  skill : SkillParams -> Graded (Filesystem * Config) ToolResult

  -- Requires:
  -- 1. Filesystem access to read skill files
  -- 2. Config access to locate skill directories
@

== Skill Structure

Skills are markdown files with metadata:
@
  ---
  name: skill-name
  description: Brief description of the skill
  ---

  # Skill: skill-name

  Detailed instructions and guidance...
@

== Use Cases

1. Complex multi-step tasks
2. Tasks requiring specialized knowledge
3. Consistent procedures across projects
4. Training and onboarding guidance

== Permission Model

Skills can be restricted per agent:
@
  skill: { allow: ["approved-skill"], deny: ["dangerous-skill"] }
@
-}
module Tool.Skill
  ( -- * Tool Interface
    SkillParams(..)
  , execute
  , skillTool
    -- * Skill Types
  , SkillInfo(..)
  , SkillContent(..)
    -- * Skill Registry
  , getAllSkills
  , getSkill
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, class EncodeJson, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..))

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Skill metadata.

@
  record SkillInfo where
    name        : String    -- Skill identifier
    description : String    -- Brief description
    location    : String    -- Path to skill file
@
-}
type SkillInfo =
  { name :: String
  , description :: String
  , location :: String
  }

{-| Parsed skill content.

@
  record SkillContent where
    info    : SkillInfo
    content : String      -- Markdown content
    baseDir : String      -- Directory containing skill
@
-}
type SkillContent =
  { info :: SkillInfo
  , content :: String
  , baseDir :: String
  }

{-| Parameters for skill tool.

@
  record SkillParams where
    name : String   -- The skill identifier from available_skills
@
-}
type SkillParams =
  { name :: String
  }

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

{-| Execute skill tool.

Loads and returns the content of the specified skill.
-}
execute :: SkillParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Find skill by name
  -- 2. Check agent permissions
  -- 3. Read skill file
  -- 4. Parse markdown
  -- 5. Return formatted output
  
  skillResult <- getSkill params.name
  case skillResult of
    Nothing -> pure $ mkErrorResult $
      "Skill \"" <> params.name <> "\" not found."
    Just skill -> pure
      { title: "Loaded skill: " <> skill.info.name
      , metadata: encodeJson
          { name: skill.info.name
          , dir: skill.baseDir
          }
      , output: formatSkillOutput skill
      , attachments: Nothing
      }

{-| Tool registration. -}
skillTool :: ToolInfo
skillTool =
  { id: "skill"
  , description: skillDescription
  , parameters: encodeJson skillSchema
  , execute: \json ctx ->
      case decodeSkillParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationError
  }

-- ============================================================================
-- SKILL REGISTRY
-- ============================================================================

{-| Get all available skills.

Scans configured directories for skill files.
-}
getAllSkills :: Aff (Array SkillInfo)
getAllSkills = do
  -- TODO: Scan skill directories
  pure []

{-| Get a specific skill by name. -}
getSkill :: String -> Aff (Maybe SkillContent)
getSkill name = do
  -- TODO: Find and parse skill file
  pure Nothing

-- ============================================================================
-- FORMATTING
-- ============================================================================

{-| Format skill output for display. -}
formatSkillOutput :: SkillContent -> String
formatSkillOutput skill = String.joinWith "\n"
  [ "## Skill: " <> skill.info.name
  , ""
  , "**Base directory**: " <> skill.baseDir
  , ""
  , skill.content
  ]

-- ============================================================================
-- HELPERS
-- ============================================================================

skillDescription :: String
skillDescription = String.joinWith " "
  [ "Load a skill to get detailed instructions for a specific task."
  , "No skills are currently available."
  ]

skillSchema :: { type :: String }
skillSchema = { type: "object" }

decodeSkillParams :: Json -> Either String SkillParams
decodeSkillParams _ = notImplemented "decodeSkillParams"

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Skill Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid skill parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
