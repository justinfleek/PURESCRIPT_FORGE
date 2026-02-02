{-|
Module      : Tool.Question
Description : Interactive user questioning tool
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Question Tool

This tool enables the AI assistant to ask the user questions during
execution. It supports single and multiple choice questions with
custom answer options.

== Coeffect Equation

@
  question : QuestionParams -> Graded UI (Array Answer)

  -- Requires:
  -- 1. UI access for displaying questions
  -- 2. Session context for routing answers
@

== Use Cases

1. Gathering user preferences or requirements
2. Clarifying ambiguous instructions
3. Getting decisions on implementation choices
4. Offering choices about what direction to take

== Question Structure

@
  +------------------------------------------+
  |  Header (max 30 chars)                   |
  +------------------------------------------+
  |  Question: Complete question text        |
  |                                          |
  |  [ ] Option 1 - Description              |
  |  [ ] Option 2 - Description              |
  |  [ ] Option 3 - Description              |
  |                                          |
  |  [Type your own answer] (if custom)      |
  +------------------------------------------+
@
-}
module Tool.Question
  ( -- * Tool Interface
    QuestionParams(..)
  , QuestionResult(..)
  , execute
  , questionTool
    -- * Question Types
  , QuestionDef(..)
  , Option(..)
  , Answer(..)
    -- * Formatting
  , formatAnswer
  , formatAnswers
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, class EncodeJson, class DecodeJson, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..))

-- ============================================================================
-- TYPES
-- ============================================================================

{-| Question option definition.

@
  record Option where
    label       : String  -- Display text (1-5 words, concise)
    description : String  -- Explanation of choice
@
-}
type Option =
  { label :: String
  , description :: String
  }

{-| Single question definition.

@
  record QuestionDef where
    question : String           -- Complete question
    header   : String           -- Very short label (max 30 chars)
    options  : Array Option     -- Available choices
    multiple : Maybe Boolean    -- Allow selecting multiple
@
-}
type QuestionDef =
  { question :: String
  , header :: String
  , options :: Array Option
  , multiple :: Maybe Boolean
  }

{-| Parameters for question tool.

@
  record QuestionParams where
    questions : Array QuestionDef
@
-}
type QuestionParams =
  { questions :: Array QuestionDef
  }

{-| Answer to a question (array of selected labels). -}
type Answer = Array String

{-| Result from question tool. -}
type QuestionResult =
  { title :: String
  , output :: String
  , metadata :: { answers :: Array Answer }
  }

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

{-| Execute question tool.

Displays questions to user and collects answers.
Returns formatted output with user responses.
-}
execute :: QuestionParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate parameters
  -- 2. Request answers from UI via session
  -- 3. Collect and format responses
  let numQuestions = Array.length params.questions
  let plural = if numQuestions > 1 then "s" else ""
  
  -- TODO: Actually ask questions via session/UI bridge
  -- For now, return placeholder indicating questions were asked
  pure
    { title: "Asked " <> show numQuestions <> " question" <> plural
    , metadata: encodeJson
        { questions: params.questions
        , answered: false
        }
    , output: "Questions submitted to user. Awaiting responses..."
    , attachments: Nothing
    }

{-| Tool registration. -}
questionTool :: ToolInfo
questionTool =
  { id: "question"
  , description: questionDescription
  , parameters: encodeJson questionSchema
  , execute: \json ctx ->
      case decodeQuestionParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationError
  }

-- ============================================================================
-- FORMATTING
-- ============================================================================

{-| Format a single answer for display. -}
formatAnswer :: Answer -> String
formatAnswer answer =
  case Array.length answer of
    0 -> "Unanswered"
    _ -> String.joinWith ", " answer

{-| Format all answers for output. -}
formatAnswers :: Array QuestionDef -> Array Answer -> String
formatAnswers questions answers =
  let pairs = Array.zip questions answers
      formatted = map formatPair pairs
  in String.joinWith ", " formatted
  where
    formatPair :: { fst :: QuestionDef, snd :: Answer } -> String
    formatPair { fst: q, snd: a } =
      "\"" <> q.question <> "\"=\"" <> formatAnswer a <> "\""

-- ============================================================================
-- HELPERS
-- ============================================================================

questionDescription :: String
questionDescription = String.joinWith "\n"
  [ "Use this tool when you need to ask the user questions during execution."
  , "This allows you to:"
  , "1. Gather user preferences or requirements"
  , "2. Clarify ambiguous instructions"
  , "3. Get decisions on implementation choices"
  , "4. Offer choices about what direction to take"
  , ""
  , "Usage notes:"
  , "- When custom is enabled (default), a 'Type your own answer' option is added"
  , "- Answers are returned as arrays of labels"
  , "- Set multiple: true to allow selecting more than one"
  , "- If you recommend a specific option, make it first and add '(Recommended)'"
  ]

questionSchema :: { type :: String, properties :: {} }
questionSchema =
  { type: "object"
  , properties: {}  -- TODO: Full JSON Schema
  }

decodeQuestionParams :: Json -> Either String QuestionParams
decodeQuestionParams json = notImplemented "decodeQuestionParams"

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Question Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationError :: Json -> String
formatValidationError _ = "Invalid question parameters"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
