{-|
Module      : Forge.Tool.Skill
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
module Forge.Tool.Skill
  ( -- * Tool Interface
    SkillParams
  , execute
  , skillTool
    -- * Skill Types
  , SkillInfo
  , SkillContent
    -- * Skill Registry
  , getAllSkills
  , getSkill
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson, (.:), printJsonDecodeError)
import Data.Traversable (traverse)
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

-- | Directory entry from FFI
type DirEntry =
  { name :: String
  , isDirectory :: Boolean
  }

-- ============================================================================
-- FFI
-- ============================================================================

-- | FFI for directory listing
foreign import listDirectoryFFI :: String -> Aff (Either String (Array DirEntry))

-- | FFI for file reading
foreign import readFileFFI :: String -> Aff (Either String String)

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
  
  skillResult <- getSkill params.name ctx.workspaceRoot
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
  , parameters: skillSchema
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
getAllSkills :: String -> Aff (Array SkillInfo)
getAllSkills workspaceRoot = do
  -- Scan skill directories
  allSkills <- traverse (scanDirectory workspaceRoot) skillDirectories
  pure $ Array.concat allSkills

scanDirectory :: String -> String -> Aff (Array SkillInfo)
scanDirectory workspaceRoot dir = do
  let fullDir = workspaceRoot <> "/" <> dir
  listResult <- listDirectoryFFI fullDir
  case listResult of
    Left _ -> pure []  -- Directory doesn't exist, skip
    Right entries -> do
      -- Skills are in subdirectories: <dir>/<skill-name>/SKILL.md
      let skillDirs = Array.mapMaybe (\e -> 
            if e.isDirectory then Just (fullDir <> "/" <> e.name) else Nothing
          ) entries
      -- Scan each skill subdirectory for SKILL.md
      allSkills <- traverse scanSkillSubdir skillDirs
      pure $ Array.concat allSkills

scanSkillSubdir :: String -> Aff (Array SkillInfo)
scanSkillSubdir skillDir = do
  listResult <- listDirectoryFFI skillDir
  case listResult of
    Left _ -> pure []
    Right entries -> do
      -- Look for SKILL.md file
      case Array.find (\e -> not e.isDirectory && e.name == "SKILL.md") entries of
        Nothing -> pure []
        Just _ -> do
          let skillFile = skillDir <> "/SKILL.md"
          skillResult <- parseSkillFile skillFile skillDir
          pure $ case skillResult of
            Just skill -> [skill]
            Nothing -> []

{-| Get a specific skill by name. -}
getSkill :: String -> String -> Aff (Maybe SkillContent)
getSkill name workspaceRoot = do
  -- Find skill file in directories
  allSkills <- getAllSkills workspaceRoot
  case Array.find (\s -> s.name == name) allSkills of
    Nothing -> pure Nothing
    Just skillInfo -> do
      -- Read and parse skill file
      readResult <- readFileFFI skillInfo.location
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
parseSkillFile :: String -> String -> Aff (Maybe SkillInfo)
parseSkillFile filePath skillDir = do
  readResult <- readFileFFI filePath
  case readResult of
    Left _ -> pure Nothing
    Right content -> do
      -- Parse frontmatter and extract name/description
      let skillName = extractSkillNameFromDir skillDir
      let description = extractDescription content
      pure $ Just
        { name: skillName
        , description: description
        , location: filePath
        }

-- | Extract skill name from directory path (last component)
extractSkillNameFromDir :: String -> String
extractSkillNameFromDir path =
  let parts = String.split (String.Pattern "/") path
  in Array.last parts # fromMaybe path

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
  [ "<skill_content name=\"" <> skill.info.name <> "\">"
  , ""
  , "**Base directory**: " <> skill.baseDir
  , ""
  , skill.content
  , ""
  , "</skill_content>"
  ]

-- ============================================================================
-- HELPERS
-- ============================================================================

skillDescription :: String
skillDescription = String.joinWith " "
  [ "Load a specialized skill that provides domain-specific instructions and workflows."
  , "When you recognize that a task matches one of the available skills, use this tool to load the full skill instructions."
  ]

skillSchema :: Json
skillSchema = encodeJson
  { "type": "object"
  , "properties":
      { "name": 
          { "type": "string"
          , "description": "The name of the skill from available_skills"
          }
      }
  , "required": ["name"]
  }

decodeSkillParams :: Json -> Either String SkillParams
decodeSkillParams json =
  case decodeSkillParamsImpl json of
    Left err -> Left (printJsonDecodeError err)
    Right result -> Right result
  where
    decodeSkillParamsImpl j = do
      obj <- decodeJson j
      name <- obj .: "name"
      pure { name }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Skill Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid skill parameters"
