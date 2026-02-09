-- | OpenAI Error types
-- | Ported from: openai-error.ts
module Forge.Provider.SDK.OpenAICompatible.Responses.OpenAIError where

import Prelude

import Data.Argonaut (Json, jsonParser, decodeJson, toString, toObject)
import Data.Argonaut.Decode.Class (class DecodeJson)
import Data.Either (Either(..), hush)
import Data.Maybe (Maybe(..), fromMaybe)
import Foreign.Object as Object

-- | OpenAI API error
type OpenAIError =
  { message :: String
  , "type" :: String
  , code :: Maybe String
  , param :: Maybe String
  }

-- | Error response wrapper
type OpenAIErrorResponse =
  { error :: OpenAIError
  }

-- | Parse error from JSON response string
-- | Expects format: { "error": { "message": "...", "type": "...", "code": "...", "param": "..." } }
parseError :: String -> Maybe OpenAIError
parseError jsonStr = do
  json <- hush (jsonParser jsonStr)
  obj <- toObject json
  errorJson <- Object.lookup "error" obj
  errorObj <- toObject errorJson
  message <- Object.lookup "message" errorObj >>= toString
  errType <- Object.lookup "type" errorObj >>= toString
  let code = Object.lookup "code" errorObj >>= toString
  let param = Object.lookup "param" errorObj >>= toString
  pure { message, "type": errType, code, param }

-- | Parse error from a Json value directly
parseErrorFromJson :: Json -> Maybe OpenAIError
parseErrorFromJson json = do
  obj <- toObject json
  errorJson <- Object.lookup "error" obj
  errorObj <- toObject errorJson
  message <- Object.lookup "message" errorObj >>= toString
  errType <- Object.lookup "type" errorObj >>= toString
  let code = Object.lookup "code" errorObj >>= toString
  let param = Object.lookup "param" errorObj >>= toString
  pure { message, "type": errType, code, param }

-- | Format error for display
formatError :: OpenAIError -> String
formatError err = err."type" <> ": " <> err.message

-- | Format error with optional code
formatErrorVerbose :: OpenAIError -> String
formatErrorVerbose err =
  let base = err."type" <> ": " <> err.message
      codeStr = case err.code of
        Just c -> " (code: " <> c <> ")"
        Nothing -> ""
      paramStr = case err.param of
        Just p -> " [param: " <> p <> "]"
        Nothing -> ""
  in base <> codeStr <> paramStr
