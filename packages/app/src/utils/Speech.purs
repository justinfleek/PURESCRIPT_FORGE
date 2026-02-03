-- | Speech recognition utilities using Web Speech API
-- | Migrated from: forge-dev/packages/app/src/utils/speech.ts (329 lines)
module Sidepanel.Utils.Speech
  ( SpeechRecognition
  , SpeechRecognitionState
  , createSpeechRecognition
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Timer (setTimeout, clearTimeout, TimeoutId)

-- | Speech recognition state
type SpeechRecognitionState =
  { isRecording :: Boolean
  , committed :: String
  , interim :: String
  }

-- | Speech recognition callbacks
type SpeechRecognitionCallbacks =
  { onFinal :: Maybe (String -> Effect Unit)
  , onInterim :: Maybe (String -> Effect Unit)
  }

-- | Speech recognition result
type SpeechRecognition =
  { isSupported :: Effect Boolean
  , isRecording :: Effect Boolean
  , committed :: Effect String
  , interim :: Effect String
  , start :: Effect Unit
  , stop :: Effect Unit
  }

-- | Recognition result from browser API
type RecognitionResult =
  { transcript :: String
  , isFinal :: Boolean
  }

-- | Commit delay in milliseconds
commitDelay :: Int
commitDelay = 250

-- | Append segment to base text with proper spacing
appendSegment :: String -> String -> String
appendSegment base addition =
  let trimmed = trim addition
  in if isEmpty trimmed then base
     else if isEmpty base then trimmed
     else 
       let needsSpace = hasTrailingNonSpace base && not (startsWithPunctuation trimmed)
       in base <> (if needsSpace then " " else "") <> trimmed

-- | Extract suffix from hypothesis that extends committed text
extractSuffix :: String -> String -> String
extractSuffix committed hypothesis =
  let cleanHypothesis = trim hypothesis
  in if isEmpty cleanHypothesis then ""
     else
       let baseTokens = if isEmpty (trim committed) then [] else split (trim committed)
           hypothesisTokens = split cleanHypothesis
           matchIndex = findMatchEnd baseTokens hypothesisTokens 0
       in if matchIndex < length baseTokens then ""
          else joinWith " " (drop matchIndex hypothesisTokens)

-- | Find where base tokens end in hypothesis
findMatchEnd :: Array String -> Array String -> Int -> Int
findMatchEnd base hypo idx
  | idx >= length base = idx
  | idx >= length hypo = idx
  | index base idx /= index hypo idx = idx
  | otherwise = findMatchEnd base hypo (idx + 1)

-- | Create speech recognition instance
createSpeechRecognition :: { lang :: Maybe String } -> SpeechRecognitionCallbacks -> Effect SpeechRecognition
createSpeechRecognition opts callbacks = do
  -- Check browser support
  supported <- hasSpeechSupport
  
  -- Create state refs
  stateRef <- Ref.new { isRecording: false, committed: "", interim: "" }
  shouldContinueRef <- Ref.new false
  committedTextRef <- Ref.new ""
  sessionCommittedRef <- Ref.new ""
  pendingHypothesisRef <- Ref.new ""
  lastInterimSuffixRef <- Ref.new ""
  shrinkCandidateRef <- Ref.new Nothing
  commitTimerRef <- Ref.new Nothing
  restartTimerRef <- Ref.new Nothing
  
  -- Get recognition instance if supported
  recognitionRef <- if supported
                    then createRecognitionInstance opts >>= \r -> Ref.new (Just r)
                    else Ref.new Nothing
  
  let
    cancelPendingCommit :: Effect Unit
    cancelPendingCommit = do
      timer <- Ref.read commitTimerRef
      case timer of
        Nothing -> pure unit
        Just t -> do
          clearTimeout t
          Ref.write Nothing commitTimerRef
    
    clearRestart :: Effect Unit
    clearRestart = do
      timer <- Ref.read restartTimerRef
      case timer of
        Nothing -> pure unit
        Just t -> do
          clearTimeout t
          Ref.write Nothing restartTimerRef
    
    commitSegment :: String -> Effect Unit
    commitSegment segment = do
      committed <- Ref.read committedTextRef
      let next = appendSegment committed segment
      when (next /= committed) do
        Ref.write next committedTextRef
        Ref.modify (_ { committed = next }) stateRef
        case callbacks.onFinal of
          Just cb -> cb (trim segment)
          Nothing -> pure unit
    
    promotePending :: Effect Unit
    promotePending = do
      pending <- Ref.read pendingHypothesisRef
      when (not (isEmpty pending)) do
        sessionCommitted <- Ref.read sessionCommittedRef
        let suffix = extractSuffix sessionCommitted pending
        when (not (isEmpty suffix)) do
          let nextSession = appendSegment sessionCommitted suffix
          Ref.write nextSession sessionCommittedRef
          commitSegment suffix
        Ref.write "" pendingHypothesisRef
        Ref.write "" lastInterimSuffixRef
        Ref.write Nothing shrinkCandidateRef
        Ref.modify (_ { interim = "" }) stateRef
        case callbacks.onInterim of
          Just cb -> cb ""
          Nothing -> pure unit
    
    applyInterim :: String -> String -> Effect Unit
    applyInterim suffix hypothesis = do
      cancelPendingCommit
      Ref.write hypothesis pendingHypothesisRef
      Ref.write suffix lastInterimSuffixRef
      Ref.write Nothing shrinkCandidateRef
      Ref.modify (_ { interim = suffix }) stateRef
      
      case callbacks.onInterim of
        Just cb -> do
          committed <- Ref.read committedTextRef
          cb (if isEmpty suffix then "" else appendSegment committed suffix)
        Nothing -> pure unit
      
      when (not (isEmpty suffix)) do
        -- Schedule commit after delay
        timer <- setTimeout commitDelay do
          currentPending <- Ref.read pendingHypothesisRef
          when (currentPending == hypothesis) do
            sessionCommitted <- Ref.read sessionCommittedRef
            let currentSuffix = extractSuffix sessionCommitted currentPending
            when (not (isEmpty currentSuffix)) do
              let nextSession = appendSegment sessionCommitted currentSuffix
              Ref.write nextSession sessionCommittedRef
              commitSegment currentSuffix
            Ref.write "" pendingHypothesisRef
            Ref.write "" lastInterimSuffixRef
            Ref.write Nothing shrinkCandidateRef
            Ref.modify (_ { interim = "" }) stateRef
            case callbacks.onInterim of
              Just cb -> cb ""
              Nothing -> pure unit
        Ref.write (Just timer) commitTimerRef
  
  pure
    { isSupported: pure supported
    , isRecording: Ref.read stateRef <#> _.isRecording
    , committed: Ref.read stateRef <#> _.committed
    , interim: Ref.read stateRef <#> _.interim
    , start: do
        maybeRecog <- Ref.read recognitionRef
        case maybeRecog of
          Nothing -> pure unit
          Just recog -> do
            clearRestart
            Ref.write true shouldContinueRef
            Ref.write "" sessionCommittedRef
            Ref.write "" pendingHypothesisRef
            cancelPendingCommit
            Ref.write "" lastInterimSuffixRef
            Ref.write Nothing shrinkCandidateRef
            Ref.modify (_ { interim = "" }) stateRef
            startRecognition recog
    , stop: do
        maybeRecog <- Ref.read recognitionRef
        case maybeRecog of
          Nothing -> pure unit
          Just recog -> do
            Ref.write false shouldContinueRef
            clearRestart
            promotePending
            cancelPendingCommit
            Ref.write "" lastInterimSuffixRef
            Ref.write Nothing shrinkCandidateRef
            Ref.modify (_ { interim = "" }) stateRef
            case callbacks.onInterim of
              Just cb -> cb ""
              Nothing -> pure unit
            stopRecognition recog
    }

-- | Foreign imports for browser APIs
foreign import hasSpeechSupport :: Effect Boolean
foreign import createRecognitionInstance :: { lang :: Maybe String } -> Effect RecognitionInstance
foreign import startRecognition :: RecognitionInstance -> Effect Unit
foreign import stopRecognition :: RecognitionInstance -> Effect Unit

-- | Recognition instance type (opaque)
foreign import data RecognitionInstance :: Type

-- | String helpers
foreign import trim :: String -> String
foreign import isEmpty :: String -> Boolean
foreign import hasTrailingNonSpace :: String -> Boolean
foreign import startsWithPunctuation :: String -> Boolean
foreign import split :: String -> Array String
foreign import joinWith :: String -> Array String -> String
foreign import length :: forall a. Array a -> Int
foreign import index :: forall a. Array a -> Int -> a
foreign import drop :: forall a. Int -> Array a -> Array a
