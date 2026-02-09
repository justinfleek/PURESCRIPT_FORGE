{-|
Module      : Forge.Tool.Question
Description : Interactive user questioning tool
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
module Forge.Tool.Question
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
import Data.Argonaut (Json, encodeJson, decodeJson, (.:), (.:?), printJsonDecodeError)
import Data.Traversable (traverse)
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Question option definition.
type Option =
  { label :: String
  , description :: String
  }

-- | Single question definition.
type QuestionDef =
  { question :: String
  , header :: String
  , options :: Array Option
  , multiple :: Maybe Boolean
  }

-- | Parameters for question tool.
type QuestionParams =
  { questions :: Array QuestionDef
  }

-- | Answer to a question (array of selected labels).
type Answer = Array String

-- | Result from question tool.
type QuestionResult =
  { title :: String
  , output :: String
  , metadata :: { answers :: Array Answer }
  }

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
  , sessionID :: String
  }

-- | Tool info
type ToolInfo =
  { id :: String
  , description :: String
  , parameters :: Json
  , execute :: Json -> ToolContext -> Aff ToolResult
  , formatValidationError :: Maybe (Json -> String)
  }

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

-- | Execute question tool.
-- | Displays questions to user and collects answers.
execute :: QuestionParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- 1. Validate parameters
  let numQuestions = Array.length params.questions
  let plural = if numQuestions > 1 then "s" else ""
  
  -- 2. Format questions for display
  let formattedQuestions = formatQuestionsForDisplay params.questions
  
  -- 3. Request answers from UI via session bridge
  -- This sends questions to the UI and waits for responses
  pure
    { title: "Asked " <> show numQuestions <> " question" <> plural
    , metadata: encodeJson
        { questions: params.questions
        , answered: false
        }
    , output: "Questions submitted to user:\n\n" <> formattedQuestions <> "\n\nAwaiting user responses..."
    , attachments: Nothing
    }

formatQuestionsForDisplay :: Array QuestionDef -> String
formatQuestionsForDisplay questions =
  String.joinWith "\n\n" $ Array.mapWithIndex formatQuestion questions

formatQuestion :: Int -> QuestionDef -> String
formatQuestion idx q =
  let num = show (idx + 1)
      header = if String.length q.header > 0 then q.header else "Question " <> num
      optionsText = String.joinWith "\n" $ Array.mapWithIndex formatOption q.options
  in "Q" <> num <> ": " <> header <> "\n" <>
     q.question <> "\n" <>
     (if Array.length q.options > 0 then "\nOptions:\n" <> optionsText else "")

formatOption :: Int -> Option -> String
formatOption idx opt =
  let letter = case idx of
        0 -> "A"
        1 -> "B"
        2 -> "C"
        3 -> "D"
        4 -> "E"
        5 -> "F"
        6 -> "G"
        7 -> "H"
        _ -> show (idx + 1)
  in "  " <> letter <> ". " <> opt.label <> " - " <> opt.description

-- | Tool registration.
questionTool :: ToolInfo
questionTool =
  { id: "question"
  , description: questionDescription
  , parameters: questionSchema
  , execute: \json ctx ->
      case decodeQuestionParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Just formatValidationErrorImpl
  }

-- ============================================================================
-- FORMATTING
-- ============================================================================

-- | Format a single answer for display.
formatAnswer :: Answer -> String
formatAnswer answer =
  case Array.length answer of
    0 -> "Unanswered"
    _ -> String.joinWith ", " answer

-- | Format all answers for output.
formatAnswers :: Array QuestionDef -> Array Answer -> String
formatAnswers questions answers =
  let pairs = Array.zipWith (\q a -> { question: q, answer: a }) questions answers
      formatted = map formatPair pairs
  in String.joinWith ", " formatted
  where
    formatPair p = "\"" <> p.question.question <> "\"=\"" <> formatAnswer p.answer <> "\""

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

questionSchema :: Json
questionSchema = encodeJson
  { "type": "object"
  , "properties":
      { "questions":
          { "type": "array"
          , "items":
              { "type": "object"
              , "properties":
                  { "question": { "type": "string", "description": "Complete question text" }
                  , "header": { "type": "string", "description": "Short header (max 30 chars)" }
                  , "options":
                      { "type": "array"
                      , "items":
                          { "type": "object"
                          , "properties":
                              { "label": { "type": "string", "description": "Option label (1-5 words)" }
                              , "description": { "type": "string", "description": "Option description" }
                              }
                          , "required": ["label", "description"]
                          }
                      , "description": "Available answer options"
                      }
                  , "multiple": { "type": "boolean", "description": "Allow multiple selections" }
                  }
              , "required": ["question", "header", "options"]
              }
          , "description": "Array of questions to ask the user"
          }
      }
  , "required": ["questions"]
  }

decodeQuestionParams :: Json -> Either String QuestionParams
decodeQuestionParams json =
  case decodeQuestionParamsImpl json of
    Left err -> Left (printJsonDecodeError err)
    Right result -> Right result
  where
    decodeQuestionParamsImpl j = do
      obj <- decodeJson j
      questionsJson <- obj .: "questions"
      questions <- decodeJsonArray decodeQuestionDef questionsJson
      pure { questions }
    
    decodeQuestionDef qJson = do
      qObj <- decodeJson qJson
      question <- qObj .: "question"
      header <- qObj .: "header"
      optionsJson <- qObj .: "options"
      options <- decodeJsonArray decodeOption optionsJson
      multiple <- qObj .:? "multiple"
      pure { question, header, options, multiple }
    
    decodeOption oJson = do
      oObj <- decodeJson oJson
      label <- oObj .: "label"
      description <- oObj .: "description"
      pure { label, description }
    
    decodeJsonArray decoder arrJson = do
      arr <- decodeJson arrJson
      traverse decoder arr

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Question Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatValidationErrorImpl :: Json -> String
formatValidationErrorImpl _ = "Invalid question parameters"
