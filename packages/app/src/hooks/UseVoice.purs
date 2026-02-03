-- | Voice recording and transcription hook
-- | Migrated from forge-dev/packages/app/src/hooks/use-voice.ts
module Forge.App.Hooks.UseVoice
  ( VoiceConfig
  , VoiceState
  , useVoice
  , speakText
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, launchAff_, makeAff, nonCanceler)
import Effect.Class (liftEffect)
import Effect.Ref (Ref, new, read, write)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Web.HTML (window)
import Web.HTML.Window (localStorage)
import Web.Storage.Storage (getItem)

type VoiceConfig =
  { onTranscript :: String -> Effect Unit
  , onError :: Maybe (String -> Effect Unit)
  , language :: Maybe String
  }

type VoiceState =
  { recording :: Boolean
  , processing :: Boolean
  , startRecording :: Effect Unit
  , stopRecording :: Effect Unit
  , toggleRecording :: Effect Unit
  }

-- | Create a voice recording hook
useVoice :: VoiceConfig -> Effect VoiceState
useVoice config = do
  recordingRef <- new false
  processingRef <- new false
  recorderRef <- new (Nothing :: Maybe MediaRecorder)
  chunksRef <- new ([] :: Array Blob)
  
  let
    startRecording = launchAff_ do
      result <- getUserMedia { audio: true }
      case result of
        Left err -> liftEffect $ handleError config err
        Right stream -> liftEffect do
          recorder <- createMediaRecorder stream "audio/webm"
          write (Just recorder) recorderRef
          write [] chunksRef
          
          setOnDataAvailable recorder \blob -> do
            chunks <- read chunksRef
            write (chunks <> [blob]) chunksRef
          
          setOnStop recorder do
            write false recordingRef
            write true processingRef
            chunks <- read chunksRef
            launchAff_ do
              let audioBlob = createBlob chunks "audio/webm"
              lang <- liftEffect $ getLang config
              transcriptResult <- transcribeAudio audioBlob lang
              liftEffect do
                write false processingRef
                case transcriptResult of
                  Left err -> handleError config err
                  Right text -> config.onTranscript text
                stopAllTracks stream
          
          startMediaRecorder recorder
          write true recordingRef
    
    stopRecording = do
      mRecorder <- read recorderRef
      case mRecorder of
        Just recorder -> stopMediaRecorder recorder
        Nothing -> pure unit
    
    toggleRecording = do
      isRecording <- read recordingRef
      if isRecording then stopRecording else startRecording
  
  pure
    { recording: false  -- Would need reactive state
    , processing: false
    , startRecording
    , stopRecording
    , toggleRecording
    }

-- | Speak text using TTS
speakText :: String -> String -> Aff Unit
speakText text voice = do
  endpoint <- liftEffect getTTSEndpoint
  case endpoint of
    Nothing -> speakWithBrowserTTS text
    Just ep -> speakWithAPI ep text voice

-- FFI types and functions
foreign import data MediaRecorder :: Type
foreign import data MediaStream :: Type
foreign import data Blob :: Type

foreign import getUserMedia :: { audio :: Boolean } -> Aff (Either String MediaStream)
foreign import createMediaRecorder :: MediaStream -> String -> Effect MediaRecorder
foreign import startMediaRecorder :: MediaRecorder -> Effect Unit
foreign import stopMediaRecorder :: MediaRecorder -> Effect Unit
foreign import setOnDataAvailable :: MediaRecorder -> (Blob -> Effect Unit) -> Effect Unit
foreign import setOnStop :: MediaRecorder -> Effect Unit -> Effect Unit
foreign import stopAllTracks :: MediaStream -> Effect Unit
foreign import createBlob :: Array Blob -> String -> Blob

foreign import transcribeAudio :: Blob -> String -> Aff (Either String String)
foreign import speakWithBrowserTTS :: String -> Aff Unit
foreign import speakWithAPI :: String -> String -> String -> Aff Unit

-- Helpers
getLang :: VoiceConfig -> Effect String
getLang config = pure $ case config.language of
  Just l -> l
  Nothing -> "en"

handleError :: VoiceConfig -> String -> Effect Unit
handleError config err = case config.onError of
  Just handler -> handler err
  Nothing -> pure unit

getWhisperEndpoint :: Effect (Maybe String)
getWhisperEndpoint = do
  w <- window
  storage <- localStorage w
  getItem "forge-voice-endpoint" storage

getTTSEndpoint :: Effect (Maybe String)
getTTSEndpoint = do
  w <- window
  storage <- localStorage w
  getItem "forge-tts-endpoint" storage
