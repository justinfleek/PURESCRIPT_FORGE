{-|
Module      : Sidepanel.Components.InlineSuggestions.ProviderIntegration
Description : Integration with Provider system for AI model calls

Wires InlineSuggestions to the Provider system for actual AI model calls.
-}
module Sidepanel.Components.InlineSuggestions.ProviderIntegration where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String as String
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Class (liftEffect)
import Effect (Effect)

import Opencode.Provider.Provider as Provider
import Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesLanguageModel as OpenAI
import Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIResponsesAPITypes as APITypes
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( SuggestionContext
  , InlineSuggestion
  , Position
  , Range
  , CompletionKind(..)
  , EditorState
  )
import Effect.Ref (Ref as EffectRef)
import Effect.Ref as Ref

-- | Provider integration state
type ProviderIntegrationState =
  { providerState :: Ref Provider.ProviderState
  , defaultModel :: Maybe { providerID :: String, modelID :: String }
  }

-- | Initialize provider integration
initProviderIntegration :: Ref Provider.ProviderState -> Aff ProviderIntegrationState
initProviderIntegration providerStateRef = do
  defaultModelM <- liftEffect $ Provider.defaultModel providerStateRef
  pure
    { providerState: providerStateRef
    , defaultModel: defaultModelM
    }

-- | Generate suggestions using Provider system
generateSuggestionsWithProvider
  :: ProviderIntegrationState
  -> SuggestionContext
  -> Position
  -> Aff (Array InlineSuggestion)
generateSuggestionsWithProvider state context position = do
  -- Get default model
  case state.defaultModel of
    Nothing -> pure []  -- No model available
    Just { providerID, modelID } -> do
      -- Get model from provider
      modelM <- liftEffect $ Provider.getModel providerID modelID state.providerState
      case modelM of
        Nothing -> pure []
        Just model -> do
          -- Get language model
          languageModel <- Provider.getLanguage model state.providerState
          
          -- Convert to OpenAI config
          let config = languageModelToConfig languageModel model
          
          -- Build chat completion request
          let request = buildCompletionRequest context
          
          -- Accumulate streaming content
          contentRef <- liftEffect $ Ref.new ""
          
          -- Call streaming API with callback that accumulates content
          let callback = \chunk -> do
                -- Extract content from chunk
                case Array.head chunk.choices of
                  Nothing -> pure unit
                  Just choice -> do
                    case choice.delta.content of
                      Nothing -> pure unit
                      Just deltaContent -> do
                        current <- Ref.read contentRef
                        Ref.write (current <> deltaContent) contentRef
          
          result <- OpenAI.createStreamingChatCompletion config request callback
          
          case result of
            Left err -> pure []  -- Error - return empty suggestions
            Right response -> do
              -- Get accumulated content
              finalContent <- liftEffect $ Ref.read contentRef
              
              -- Track token usage if available
              case response.usage of
                Nothing -> pure unit
                Just usage -> do
                  -- Would record usage here
                  pure unit
              
              -- Convert to inline suggestions
              let suggestions = contentToSuggestions finalContent position context
              pure suggestions

-- | Generate FIM completion using Provider system
generateFIMWithProvider
  :: ProviderIntegrationState
  -> { prefix :: String, suffix :: String, language :: String }
  -> Position
  -> Aff InlineSuggestion
generateFIMWithProvider state { prefix, suffix, language } position = do
  -- Get default model
  case state.defaultModel of
    Nothing -> pure (emptySuggestion position)
    Just { providerID, modelID } -> do
      -- Get model from provider
      modelM <- liftEffect $ Provider.getModel providerID modelID state.providerState
      case modelM of
        Nothing -> pure (emptySuggestion position)
        Just model -> do
          -- Get language model
          languageModel <- Provider.getLanguage model state.providerState
          
          -- Convert to OpenAI config
          let config = languageModelToConfig languageModel model
          
          -- Build FIM request (prefix + suffix format)
          let fimPrompt = buildFIMPrompt prefix suffix language
          let request = buildFIMCompletionRequest fimPrompt
          
          -- Accumulate streaming content
          contentRef <- liftEffect $ Ref.new ""
          
          -- Call streaming API with callback
          let callback = \chunk -> do
                case Array.head chunk.choices of
                  Nothing -> pure unit
                  Just choice -> do
                    case choice.delta.content of
                      Nothing -> pure unit
                      Just deltaContent -> do
                        current <- Ref.read contentRef
                        Ref.write (current <> deltaContent) contentRef
          
          result <- OpenAI.createStreamingChatCompletion config request callback
          
          case result of
            Left err -> pure (emptySuggestion position)
            Right response -> do
              -- Get accumulated content
              finalContent <- liftEffect $ Ref.read contentRef
              let suggestion = completionToSuggestion finalContent position
              pure suggestion

-- | Convert LanguageModel to LanguageModelConfig
languageModelToConfig :: Provider.LanguageModel -> Provider.Model -> OpenAI.LanguageModelConfig
languageModelToConfig languageModel model =
  { model: languageModel.modelId
  , baseUrl: languageModel.config.baseUrl
  , apiKey: languageModel.config.apiKey
  , headers: languageModel.config.headers
  , timeout: languageModel.config.timeout
  , providerId: languageModel.providerId
  }

-- | Build chat completion request from suggestion context
buildCompletionRequest :: SuggestionContext -> APITypes.ChatCompletionRequest
buildCompletionRequest context =
  { model: ""  -- Will be set by config
  , messages:
      [ { role: "system"
        , content: buildSystemPrompt context
        , name: Nothing
        , tool_calls: Nothing
        , tool_call_id: Nothing
        }
      , { role: "user"
        , content: buildUserPrompt context
        , name: Nothing
        , tool_calls: Nothing
        , tool_call_id: Nothing
        }
      ]
  , temperature: Just 0.2  -- Lower temperature for code completions
  , maxTokens: Just 500
  , topP: Nothing
  , frequencyPenalty: Nothing
  , presencePenalty: Nothing
  , stop: Just ["\n\n", "```"]  -- Stop on blank lines or code blocks
  , stream: Just true
  , tools: Nothing
  , toolChoice: Nothing
  }

-- | Build FIM completion request
buildFIMCompletionRequest :: String -> APITypes.ChatCompletionRequest
buildFIMCompletionRequest prompt =
  { model: ""
  , messages:
      [ { role: "user"
        , content: prompt
        , name: Nothing
        , tool_calls: Nothing
        , tool_call_id: Nothing
        }
      ]
  , temperature: Just 0.2
  , maxTokens: Just 500
  , topP: Nothing
  , frequencyPenalty: Nothing
  , presencePenalty: Nothing
  , stop: Just ["<fim_middle>", "\n\n"]
  , stream: Just true
  , tools: Nothing
  , toolChoice: Nothing
  }

-- | Build system prompt for code completion
buildSystemPrompt :: SuggestionContext -> String
buildSystemPrompt context =
  "You are a code completion assistant. Generate concise, accurate code completions based on the context. " <>
  "Focus on completing the current line or function. Return only the completion text, no explanations."

-- | Build user prompt from context
buildUserPrompt :: SuggestionContext -> String
buildUserPrompt context =
  let imports = String.joinWith "\n" (Array.map formatImport context.imports)
      prefix = context.prefix
      suffix = context.suffix
      fileContext = "File: " <> context.currentFile.filePath <> "\n" <>
                    "Language: " <> context.currentFile.language <> "\n"
  in fileContext <>
     (if Array.length context.imports > 0 then imports <> "\n\n" else "") <>
     prefix <>
     "█" <>  -- Cursor marker
     suffix

-- | Format import statement
formatImport :: { module :: String, items :: Array String, qualified :: Boolean } -> String
formatImport imp =
  if imp.qualified then
    "import qualified " <> imp.module <> " as " <> imp.module
  else if Array.length imp.items > 0 then
    "import " <> imp.module <> " (" <> String.joinWith ", " imp.items <> ")"
  else
    "import " <> imp.module

-- | Build FIM prompt (Fill-in-the-Middle format)
buildFIMPrompt :: String -> String -> String -> String
buildFIMPrompt prefix suffix language =
  "<fim_prefix>" <> prefix <> "<fim_suffix>" <> suffix <> "<fim_middle>"

-- | Convert content string to inline suggestions
contentToSuggestions :: String -> Position -> SuggestionContext -> Array InlineSuggestion
contentToSuggestions content position context =
  if String.null content then
    []
  else
    [ { text: content
      , range:
          { start: position
          , end: calculateEndPosition position content
          }
      , confidence: 0.8
      , alternatives: []
      , completionKind: detectCompletionKind content
      }
    ]

-- | Convert choice to suggestion
choiceToSuggestion :: Position -> APITypes.ChatChoice -> Maybe InlineSuggestion
choiceToSuggestion position choice =
  case choice.message.content of
    "" -> Nothing
    content -> Just
      { text: content
      , range:
          { start: position
          , end: calculateEndPosition position content
          }
      , confidence: 0.8  -- Would calculate from model confidence if available
      , alternatives: []
      , completionKind: detectCompletionKind content
      }

-- | Extract completion from response
extractCompletion :: APITypes.ChatCompletionResponse -> String
extractCompletion response =
  case Array.head response.choices of
    Nothing -> ""
    Just choice -> fromMaybe "" choice.message.content

-- | Convert completion to suggestion
completionToSuggestion :: String -> Position -> InlineSuggestion
completionToSuggestion completion position =
  { text: completion
  , range:
      { start: position
      , end: calculateEndPosition position completion
      }
  , confidence: 0.8
  , alternatives: []
  , completionKind: SnippetCompletion
  }

-- | Calculate end position from text
calculateEndPosition :: Position -> String -> Position
calculateEndPosition start text =
  let lines = String.split (String.Pattern "\n") text
      lineCount = Array.length lines
      lastLine = fromMaybe "" (Array.last lines)
  in
    { line: start.line + lineCount - 1
    , column: if lineCount == 1 then start.column + String.length text else String.length lastLine
    }

-- | Detect completion kind from text
detectCompletionKind :: String -> CompletionKind
detectCompletionKind text =
  if String.contains (String.Pattern "function ") text ||
     String.contains (String.Pattern "=>") text ||
     String.contains (String.Pattern "::") text then
    FunctionCompletion
  else if String.contains (String.Pattern "import ") text then
    ImportCompletion
  else if String.contains (String.Pattern ":") text && String.contains (String.Pattern "=") text then
    TypeCompletion
  else
    VariableCompletion

-- | Empty suggestion placeholder
emptySuggestion :: Position -> InlineSuggestion
emptySuggestion position =
  { text: ""
  , range: { start: position, end: position }
  , confidence: 0.0
  , alternatives: []
  , completionKind: VariableCompletion
  }

-- | Generate streaming suggestions with chunk callback
generateStreamingSuggestions
  :: ProviderIntegrationState
  -> SuggestionContext
  -> Position
  -> (String -> Aff Unit)  -- Chunk callback (Aff for async updates)
  -> Aff Unit  -- Runs streaming in background
generateStreamingSuggestions state context position onChunk = do
  -- Get default model
  case state.defaultModel of
    Nothing -> pure Nothing
    Just { providerID, modelID } -> do
      -- Get model from provider
      modelM <- liftEffect $ Provider.getModel providerID modelID state.providerState
      case modelM of
        Nothing -> pure Nothing
        Just model -> do
          -- Get language model
          languageModel <- Provider.getLanguage model state.providerState
          
          -- Convert to OpenAI config
          let config = languageModelToConfig languageModel model
          
          -- Build chat completion request
          let request = buildCompletionRequest context
          
          -- Accumulate streaming content
          contentRef <- liftEffect $ Ref.new ""
          
          -- Call streaming API with callback that accumulates content and calls onChunk
          let callback = \chunk -> do
                -- Extract content from chunk
                case Array.head chunk.choices of
                  Nothing -> pure unit
                  Just choice -> do
                    case choice.delta.content of
                      Nothing -> pure unit
                      Just deltaContent -> do
                        current <- Ref.read contentRef
                        Ref.write (current <> deltaContent) contentRef
                        -- Call user-provided chunk callback
                        onChunk deltaContent
          
          result <- OpenAI.createStreamingChatCompletion config request callback
          
          case result of
            Left err -> pure unit
            Right response -> do
              -- Streaming completed, callback was called for each chunk
              pure unit

-- | Convert content to suggestion (for streaming)
contentToSuggestion :: String -> Position -> InlineSuggestion
contentToSuggestion content position =
  { text: content
  , range:
      { start: position
      , end: calculateEndPosition position content
      }
  , confidence: 0.8
  , alternatives: []
  , completionKind: detectCompletionKind content
  }
