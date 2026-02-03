-- | Voice chat page - voice-based AI interaction
-- | Migrated from: forge-dev/packages/app/src/pages/voice.tsx (298 lines)
module Sidepanel.Pages.Voice
  ( VoiceChatPage
  , VoiceChatState
  , TranscriptMessage
  , VoiceChatResponse
  ) where

import Prelude

import Data.Array as Array
import Data.DateTime (DateTime)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Web.File.Blob (Blob)

-- | Message in the voice transcript
type TranscriptMessage =
  { id :: String
  , role :: String  -- "user" | "assistant"
  , text :: String
  , timestamp :: DateTime
  , audioUrl :: Maybe String
  }

-- | Response from voice chat API
type VoiceChatResponse =
  { user_transcript :: String
  , assistant_text :: Maybe String
  , assistant_audio :: Maybe String
  , assistant_audio_format :: Maybe String
  , stt_error :: Maybe String
  , chat_error :: Maybe String
  , tts_error :: Maybe String
  }

-- | Voice chat page state
type VoiceChatState =
  { isListening :: Boolean      -- Currently recording
  , isProcessing :: Boolean     -- Processing voice message
  , isSpeaking :: Boolean       -- Assistant audio playing
  , audioLevel :: Number        -- Current audio level (0-1)
  , messages :: Array TranscriptMessage
  , voices :: Array String      -- Available TTS voices
  , selectedVoice :: String     -- Currently selected voice
  , conversationId :: String    -- Conversation session ID
  , error :: Maybe String       -- Current error message
  , mediaRecorder :: Maybe MediaRecorderHandle
  , audioChunks :: Array Blob
  }

-- | Opaque handle to MediaRecorder
foreign import data MediaRecorderHandle :: Type

-- | Initial state for voice chat
initialState :: VoiceChatState
initialState =
  { isListening: false
  , isProcessing: false
  , isSpeaking: false
  , audioLevel: 0.0
  , messages: []
  , voices: []
  , selectedVoice: "Ryan"
  , conversationId: "default"
  , error: Nothing
  , mediaRecorder: Nothing
  , audioChunks: []
  }

-- | Load available voices from API
loadVoices :: Aff (Array String)
loadVoices = do
  -- listVoices() from @/api/voice
  pure []

-- | Start recording audio from microphone
-- | 1. Request microphone permission
-- | 2. Create AudioContext for visualization
-- | 3. Create MediaRecorder for capturing
-- | 4. Start visualization loop
startRecording :: VoiceChatState -> Effect VoiceChatState
startRecording state = do
  -- Get media stream: navigator.mediaDevices.getUserMedia({ audio: true })
  -- Create AudioContext (with webkit fallback)
  -- Create AnalyserNode for audio level visualization
  -- Connect microphone -> analyser
  -- Start visualization animation loop
  -- Create MediaRecorder with audio/webm;codecs=opus
  -- Set ondataavailable handler to collect chunks
  -- Set onstop handler to process collected audio
  -- Start recorder
  pure state { isListening = true }

-- | Stop recording and process audio
stopRecording :: VoiceChatState -> Effect VoiceChatState
stopRecording state = do
  -- Stop MediaRecorder if active
  -- Clear audio level
  pure state { isListening = false, audioLevel = 0.0 }

-- | Process recorded voice message
-- | 1. Add placeholder user message
-- | 2. Send to API
-- | 3. Update user message with transcript
-- | 4. Add assistant response
-- | 5. Play audio response if available
handleVoiceMessage :: Blob -> VoiceChatState -> Aff VoiceChatState
handleVoiceMessage audioBlob state = do
  -- Set processing = true
  -- Add user message placeholder with "..."
  -- Call sendVoiceMessage API
  -- Update user message text with response.user_transcript
  -- If response.assistant_text exists:
  --   Create assistant message with audioUrl (if audio available)
  --   Play audio if available
  -- Handle any errors (stt_error, chat_error, tts_error)
  pure state

-- | Send voice message to API
sendVoiceMessage :: Blob -> String -> String -> String -> Aff VoiceChatResponse
sendVoiceMessage audioBlob conversationId voice language = do
  -- POST to voice chat endpoint
  pure { user_transcript: ""
       , assistant_text: Nothing
       , assistant_audio: Nothing
       , assistant_audio_format: Nothing
       , stt_error: Nothing
       , chat_error: Nothing
       , tts_error: Nothing
       }

-- | Play audio from data URL
playAudio :: String -> Effect Unit
playAudio audioUrl = do
  -- Create Audio element
  -- Set src to audioUrl (data:audio/format;base64,...)
  -- Set onended handler
  -- Set onerror handler
  -- Call play()
  pure unit

-- | Voice chat page component
-- |
-- | Layout:
-- | - Header with title and voice selector
-- | - Error display (if error present)
-- | - Main content:
-- |   - Audio visualizer (shows audio level)
-- |   - Microphone button (toggles recording)
-- |   - Status text (listening/processing/speaking/idle)
-- | - Transcript view (message history)
-- |
-- | State flow:
-- | 1. Idle -> Click mic -> Listening (recording)
-- | 2. Listening -> Click mic -> Processing (sending to API)
-- | 3. Processing -> Response -> Speaking (playing audio)
-- | 4. Speaking -> Audio ends -> Idle
type VoiceChatPage = Effect Unit

-- | Get status text based on current state
getStatusText :: VoiceChatState -> String -> String
getStatusText state default =
  if state.isListening then "Listening... Speak now"
  else if state.isProcessing then "Processing your message..."
  else if state.isSpeaking then "Assistant is speaking..."
  else default

-- | Audio visualization update loop
-- | Uses AnalyserNode.getByteFrequencyData to get frequency data
-- | Calculates average level from frequency bins
updateAudioLevel :: Effect Number
updateAudioLevel = do
  -- analyser.getByteFrequencyData(dataArray)
  -- sum = sum of all values in dataArray
  -- average = sum / dataArray.length / 255
  pure 0.0
