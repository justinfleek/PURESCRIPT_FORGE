-- | OpenAI Error types
module Opencode.Provider.SDK.OpenAICompatible.Responses.OpenAIError where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Argonaut (Json, jsonParser, decodeJson, (.:), (.:?))

-- | OpenAI API error
type OpenAIError =
  { message :: String
  , type :: String
  , code :: Maybe String
  , param :: Maybe String
  }

-- | Error response wrapper
type OpenAIErrorResponse =
  { error :: OpenAIError
  }

-- | Parse error from response
parseError :: String -> Maybe OpenAIError
parseError jsonStr = case jsonParser jsonStr of
  Left _ -> Nothing
  Right json -> 
    -- Try parsing as error response wrapper first
    case decodeJson json of
      Right obj -> case obj .: "error" of
        Right errJson -> case decodeJson errJson of
          Right err -> Just err
          Left _ -> Nothing
        Left _ -> Nothing
      Left _ ->
        -- Try parsing as direct error object
        case decodeJson json of
          Right obj -> case obj .: "message" of
            Right msg -> Just
              { message: msg
              , type: fromMaybe "unknown" (obj .:? "type" >>= decodeJson)
              , code: obj .:? "code" >>= decodeJson
              , param: obj .:? "param" >>= decodeJson
              }
            Left _ -> Nothing
          Left _ -> Nothing
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe def = case _ of
      Nothing -> def
      Just x -> x

-- | Format error for display
formatError :: OpenAIError -> String
formatError err = err.type <> ": " <> err.message
