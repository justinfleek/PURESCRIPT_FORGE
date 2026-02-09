-- | Voice API Client
-- | 
-- | PureScript client for voice engine API endpoints.
-- | Migrated from: packages/opencode/src/api/voice.ts

module Api.Voice
  ( VoiceChatResponse
  , TextChatResponse
  , VoiceSession
  , TTSModel
  , sendVoiceMessage
  , sendTextMessage
  , getVoiceSession
  , endVoiceSession
  , listVoices
  , listModels
  , downloadModel
  , apiBase
  ) where

import Prelude

import Affjax as AX
import Affjax.RequestBody as RequestBody
import Affjax.ResponseFormat as ResponseFormat
import Affjax.RequestHeader (RequestHeader(..))
import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Argonaut.Encode.Combinators ((:=), (~>))
import Data.Argonaut.Core as J
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.MediaType (MediaType(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)

-- | API base path
apiBase :: String
apiBase = "/api/voice"

-- | Voice chat response
-- | Returned when sending audio for transcription → AI → TTS
type VoiceChatResponse =
  { userTranscript :: String
  , sttConfidence :: Number
  , sttCostUsd :: Number
  , assistantText :: String
  , assistantThinking :: Maybe String
  , assistantAudio :: Maybe String  -- base64 encoded
  , assistantAudioFormat :: String
  , ttsCostUsd :: Number
  , totalCostUsd :: Number
  , sttError :: Maybe String
  , chatError :: Maybe String
  , ttsError :: Maybe String
  }

-- | Text chat response
-- | Returned when sending text → AI → TTS
type TextChatResponse =
  { assistantText :: String
  , assistantThinking :: Maybe String
  , assistantAudioBase64 :: String
  , assistantAudioFormat :: String
  , ttsCostUsd :: Number
  , totalCostUsd :: Number
  }

-- | Voice session
type VoiceSession =
  { id :: String
  , conversationId :: String
  , state :: String
  , totalAudioSeconds :: Number
  , startedAt :: String
  }

-- | TTS Model info
type TTSModel =
  { id :: String
  , name :: String
  , hfRepo :: String
  , status :: String
  , fileSizeMb :: Number
  , downloadedAt :: Maybe String
  }

-- | End session response
type EndSessionResponse =
  { status :: String
  , sessionId :: String
  }

-- | Download model response
type DownloadModelResponse =
  { status :: String
  , modelId :: String
  , message :: String
  }

-- | Error type for API calls
data ApiError
  = NetworkError String
  | HttpError Int String
  | DecodeError String

instance showApiError :: Show ApiError where
  show (NetworkError msg) = "Network error: " <> msg
  show (HttpError status msg) = "HTTP " <> show status <> ": " <> msg
  show (DecodeError msg) = "Decode error: " <> msg

-- | Send voice message (audio → transcript → AI → audio)
-- | Note: Blob handling requires FFI in actual implementation
sendVoiceMessage
  :: String  -- ^ Base64 encoded audio
  -> String  -- ^ Conversation ID
  -> String  -- ^ Voice name
  -> String  -- ^ Language code
  -> Aff (Either ApiError VoiceChatResponse)
sendVoiceMessage audioBase64 conversationId voice language = do
  let
    body = encodeJson
      { audio: audioBase64
      , conversation_id: conversationId
      , voice: voice
      , language: language
      }
  result <- AX.post ResponseFormat.json (apiBase <> "/chat") (Just (RequestBody.json body))
  pure $ case result of
    Left err -> Left (NetworkError (AX.printError err))
    Right response ->
      if response.status >= (AX.StatusCode 200) && response.status < (AX.StatusCode 300)
        then case decodeVoiceChatResponse response.body of
          Left err -> Left (DecodeError err)
          Right resp -> Right resp
        else Left (HttpError (unwrapStatusCode response.status) "Request failed")

-- | Send text message (text → AI → audio)
sendTextMessage
  :: String  -- ^ Text message
  -> String  -- ^ Conversation ID
  -> String  -- ^ Voice name
  -> Aff (Either ApiError TextChatResponse)
sendTextMessage text conversationId voice = do
  let
    body = encodeJson
      { text: text
      , conversation_id: conversationId
      , voice: voice
      }
  result <- AX.post ResponseFormat.json (apiBase <> "/chat/text") (Just (RequestBody.json body))
  pure $ case result of
    Left err -> Left (NetworkError (AX.printError err))
    Right response ->
      if response.status >= (AX.StatusCode 200) && response.status < (AX.StatusCode 300)
        then case decodeTextChatResponse response.body of
          Left err -> Left (DecodeError err)
          Right resp -> Right resp
        else Left (HttpError (unwrapStatusCode response.status) "Request failed")

-- | Get voice session
getVoiceSession
  :: String  -- ^ Session ID
  -> Aff (Either ApiError VoiceSession)
getVoiceSession sessionId = do
  result <- AX.get ResponseFormat.json (apiBase <> "/sessions/" <> sessionId)
  pure $ case result of
    Left err -> Left (NetworkError (AX.printError err))
    Right response ->
      if response.status >= (AX.StatusCode 200) && response.status < (AX.StatusCode 300)
        then case decodeVoiceSession response.body of
          Left err -> Left (DecodeError err)
          Right resp -> Right resp
        else Left (HttpError (unwrapStatusCode response.status) "Request failed")

-- | End voice session
endVoiceSession
  :: String  -- ^ Session ID
  -> Aff (Either ApiError EndSessionResponse)
endVoiceSession sessionId = do
  result <- AX.post ResponseFormat.json (apiBase <> "/sessions/" <> sessionId <> "/end") Nothing
  pure $ case result of
    Left err -> Left (NetworkError (AX.printError err))
    Right response ->
      if response.status >= (AX.StatusCode 200) && response.status < (AX.StatusCode 300)
        then case decodeEndSessionResponse response.body of
          Left err -> Left (DecodeError err)
          Right resp -> Right resp
        else Left (HttpError (unwrapStatusCode response.status) "Request failed")

-- | List available voices
listVoices :: Aff (Either ApiError (Array String))
listVoices = do
  result <- AX.get ResponseFormat.json (apiBase <> "/voices")
  pure $ case result of
    Left err -> Left (NetworkError (AX.printError err))
    Right response ->
      if response.status >= (AX.StatusCode 200) && response.status < (AX.StatusCode 300)
        then case decodeVoicesList response.body of
          Left err -> Left (DecodeError err)
          Right resp -> Right resp
        else Left (HttpError (unwrapStatusCode response.status) "Request failed")

-- | List available TTS models
listModels :: Aff (Either ApiError (Array TTSModel))
listModels = do
  result <- AX.get ResponseFormat.json (apiBase <> "/models")
  pure $ case result of
    Left err -> Left (NetworkError (AX.printError err))
    Right response ->
      if response.status >= (AX.StatusCode 200) && response.status < (AX.StatusCode 300)
        then case decodeModelsList response.body of
          Left err -> Left (DecodeError err)
          Right resp -> Right resp
        else Left (HttpError (unwrapStatusCode response.status) "Request failed")

-- | Download TTS model
downloadModel
  :: String  -- ^ Model ID
  -> Aff (Either ApiError DownloadModelResponse)
downloadModel modelId = do
  let body = encodeJson { model_id: modelId }
  result <- AX.post ResponseFormat.json (apiBase <> "/models/download") (Just (RequestBody.json body))
  pure $ case result of
    Left err -> Left (NetworkError (AX.printError err))
    Right response ->
      if response.status >= (AX.StatusCode 200) && response.status < (AX.StatusCode 300)
        then case decodeDownloadModelResponse response.body of
          Left err -> Left (DecodeError err)
          Right resp -> Right resp
        else Left (HttpError (unwrapStatusCode response.status) "Request failed")

-- | Helper to unwrap StatusCode
unwrapStatusCode :: AX.StatusCode -> Int
unwrapStatusCode (AX.StatusCode n) = n

-- | Decode VoiceChatResponse from JSON
decodeVoiceChatResponse :: Json -> Either String VoiceChatResponse
decodeVoiceChatResponse json = do
  obj <- J.toObject json # maybe (Left "Expected object") Right
  userTranscript <- obj .: "user_transcript"
  sttConfidence <- obj .: "stt_confidence"
  sttCostUsd <- obj .: "stt_cost_usd"
  assistantText <- obj .: "assistant_text"
  assistantThinking <- obj .:? "assistant_thinking"
  assistantAudio <- obj .:? "assistant_audio"
  assistantAudioFormat <- obj .: "assistant_audio_format"
  ttsCostUsd <- obj .: "tts_cost_usd"
  totalCostUsd <- obj .: "total_cost_usd"
  sttError <- obj .:? "stt_error"
  chatError <- obj .:? "chat_error"
  ttsError <- obj .:? "tts_error"
  pure
    { userTranscript
    , sttConfidence
    , sttCostUsd
    , assistantText
    , assistantThinking
    , assistantAudio
    , assistantAudioFormat
    , ttsCostUsd
    , totalCostUsd
    , sttError
    , chatError
    , ttsError
    }
  where
    maybe def f = case _ of
      Nothing -> def
      Just a -> f a

-- | Decode TextChatResponse from JSON
decodeTextChatResponse :: Json -> Either String TextChatResponse
decodeTextChatResponse json = do
  obj <- J.toObject json # maybe (Left "Expected object") Right
  assistantText <- obj .: "assistant_text"
  assistantThinking <- obj .:? "assistant_thinking"
  assistantAudioBase64 <- obj .: "assistant_audio_base64"
  assistantAudioFormat <- obj .: "assistant_audio_format"
  ttsCostUsd <- obj .: "tts_cost_usd"
  totalCostUsd <- obj .: "total_cost_usd"
  pure
    { assistantText
    , assistantThinking
    , assistantAudioBase64
    , assistantAudioFormat
    , ttsCostUsd
    , totalCostUsd
    }
  where
    maybe def f = case _ of
      Nothing -> def
      Just a -> f a

-- | Decode VoiceSession from JSON
decodeVoiceSession :: Json -> Either String VoiceSession
decodeVoiceSession json = do
  obj <- J.toObject json # maybe (Left "Expected object") Right
  id <- obj .: "id"
  conversationId <- obj .: "conversation_id"
  state <- obj .: "state"
  totalAudioSeconds <- obj .: "total_audio_seconds"
  startedAt <- obj .: "started_at"
  pure
    { id
    , conversationId
    , state
    , totalAudioSeconds
    , startedAt
    }
  where
    maybe def f = case _ of
      Nothing -> def
      Just a -> f a

-- | Decode EndSessionResponse from JSON
decodeEndSessionResponse :: Json -> Either String EndSessionResponse
decodeEndSessionResponse json = do
  obj <- J.toObject json # maybe (Left "Expected object") Right
  status <- obj .: "status"
  sessionId <- obj .: "session_id"
  pure { status, sessionId }
  where
    maybe def f = case _ of
      Nothing -> def
      Just a -> f a

-- | Decode voices list from JSON
decodeVoicesList :: Json -> Either String (Array String)
decodeVoicesList json = do
  obj <- J.toObject json # maybe (Left "Expected object") Right
  voices <- obj .:? "voices"
  pure $ fromMaybe [] voices
  where
    maybe def f = case _ of
      Nothing -> def
      Just a -> f a

-- | Decode models list from JSON
decodeModelsList :: Json -> Either String (Array TTSModel)
decodeModelsList json = do
  obj <- J.toObject json # maybe (Left "Expected object") Right
  models <- obj .:? "models"
  pure $ fromMaybe [] models
  where
    maybe def f = case _ of
      Nothing -> def
      Just a -> f a

-- | Decode DownloadModelResponse from JSON
decodeDownloadModelResponse :: Json -> Either String DownloadModelResponse
decodeDownloadModelResponse json = do
  obj <- J.toObject json # maybe (Left "Expected object") Right
  status <- obj .: "status"
  modelId <- obj .: "model_id"
  message <- obj .: "message"
  pure { status, modelId, message }
  where
    maybe def f = case _ of
      Nothing -> def
      Just a -> f a
