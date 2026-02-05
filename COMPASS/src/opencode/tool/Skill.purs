{-|
Module      : Tool.Skill
Description : Skill loading and management tool
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

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, class EncodeJson, encodeJson, decodeJson, (.:), (.:?))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo, ToolMetadata(..))
import Aleph.Coeffect (Resource(..))
import Tool.ASTEdit.FFI.FileIO (readFile)

-- | FFI for directory listing (reuse from Ls tool)
foreign import listDirectory :: String -> Aff (Either String (Array { name :: String, isDirectory :: Boolean }))

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

-- | Default skill directories to scan
-- | Skills are in subdirectories: <dir>/<skill-name>/SKILL.md
skillDirectories :: Array String
skillDirectories = [".cursor/skills", ".opencode/skills", ".claude/skills"]

{-| Get all available skills.

Scans configured directories for skill files.
-}
getAllSkills :: Aff (Array SkillInfo)
getAllSkills = do
  -- Scan skill directories
  allSkills <- traverse scanDirectory skillDirectories
  pure $ Array.concat allSkills
  where
    scanDirectory :: String -> Aff (Array SkillInfo)
    scanDirectory dir = do
      listResult <- listDirectory dir
      case listResult of
        Left _ -> pure []  -- Directory doesn't exist, skip
        Right entries -> do
          -- Skills are in subdirectories: <dir>/<skill-name>/SKILL.md
          let skillDirs = Array.mapMaybe (\e -> 
                if e.isDirectory then Just (dir <> "/" <> e.name) else Nothing
              ) entries
          -- Scan each skill subdirectory for SKILL.md
          allSkills <- traverse (scanSkillSubdir) skillDirs
          pure $ Array.concat allSkills
    
    scanSkillSubdir :: String -> Aff (Array SkillInfo)
    scanSkillSubdir skillDir = do
      listResult <- listDirectory skillDir
      case listResult of
        Left _ -> pure []
        Right entries -> do
          -- Look for SKILL.md file
          case Array.find (\e -> not e.isDirectory && e.name == "SKILL.md") entries of
            Nothing -> pure []
            Just _ -> do
              let skillFile = skillDir <> "/SKILL.md"
              skillResult <- parseSkillFile skillFile
              pure $ case skillResult of
                Just skill -> [skill]
                Nothing -> []

{-| Get a specific skill by name. -}
getSkill :: String -> Aff (Maybe SkillContent)
getSkill name = do
  -- Find skill file in directories
  allSkills <- getAllSkills
  case Array.find (\s -> s.name == name) allSkills of
    Nothing -> pure Nothing
    Just skillInfo -> do
      -- Read and parse skill file
      readResult <- readFile skillInfo.location
      case readResult of
        Left _ -> pure Nothing
        Right content -> do
          let baseDir = extractBaseDir skillInfo.location
          pure $ Just
            { info: skillInfo
            , content: content
            , baseDir: baseDir
            }

-- | Parse a skill file to extract metadata and content
parseSkillFile :: String -> Aff (Maybe SkillInfo)
parseSkillFile filePath = do
  readResult <- readFile filePath
  case readResult of
    Left _ -> pure Nothing
    Right content -> do
      -- Parse frontmatter and extract name/description
      let skillName = extractSkillName filePath
      let description = extractDescription content
      pure $ Just
        { name: skillName
        , description: description
        , location: filePath
        }

-- | Extract skill name from file path
extractSkillName :: String -> String
extractSkillName path =
  let parts = String.split (String.Pattern "/") path
      fileName = Array.last parts # fromMaybe path
      nameWithoutExt = String.takeWhile (_ /= '.') fileName
  in nameWithoutExt

-- | Extract description from skill content (first line after frontmatter or first paragraph)
extractDescription :: String -> String
extractDescription content =
  let lines = String.split (String.Pattern "\n") content
      -- Skip frontmatter if present
      contentLines = if Array.head lines == Just "---"
        then Array.dropWhile (_ /= "---") (Array.drop 1 lines) # Array.drop 1
        else lines
      -- Get first non-empty line as description
      firstLine = Array.find (not <<< String.null) contentLines # fromMaybe ""
  in String.take 100 firstLine

-- | Extract base directory from file path
extractBaseDir :: String -> String
extractBaseDir path =
  let parts = String.split (String.Pattern "/") path
      dirParts = Array.take (Array.length parts - 1) parts
  in String.joinWith "/" dirParts

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

skillSchema :: Json
skillSchema = encodeJson
  { type: "object"
  , properties:
      { name: { type: "string", description: "Skill identifier (name of the skill file without .md extension)" }
      }
  , required: ["name"]
  }

decodeSkillParams :: Json -> Either String SkillParams
decodeSkillParams json = do
  obj <- decodeJson json
  name <- obj .: "name" >>= decodeJson
  pure { name }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Skill Error"
  , metadata: ErrorMetadata { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid skill parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
