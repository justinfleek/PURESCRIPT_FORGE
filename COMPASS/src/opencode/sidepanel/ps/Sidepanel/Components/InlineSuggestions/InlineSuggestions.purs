{-|
Module      : Sidepanel.Components.InlineSuggestions.InlineSuggestions
Description : Main inline suggestions component

Main Halogen component that orchestrates inline code suggestions.
-}
module Sidepanel.Components.InlineSuggestions.InlineSuggestions where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( EditorState
  , InlineSuggestion
  , SuggestionRequest
  )
import Sidepanel.Components.InlineSuggestions.EditorIntegration
  ( EditorWatcherState
  , EditorChangeEvent
  , handleEditorChange
  , getCurrentEditorState
  )
import Sidepanel.Components.InlineSuggestions.IntelligentCompletion (generateIntelligentCompletions)
import Sidepanel.Components.InlineSuggestions.SuggestionRenderer
  ( SuggestionDisplayState
  , renderSuggestionComponent
  , handleSuggestionKey
  , acceptSuggestion
  , SuggestionAcceptance(..)
  , updateStreamingText
  , completeStreaming
  )
import Sidepanel.Components.InlineSuggestions.StreamingEngine (streamSuggestions)
import Sidepanel.Components.InlineSuggestions.ProviderIntegration
  ( ProviderIntegrationState
  , initProviderIntegration
  )
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Opencode.Provider.Provider (ProviderState)

-- | Component state
type State =
  { editorWatcher :: EditorWatcherState
  , displayState :: SuggestionDisplayState
  , isEnabled :: Boolean
  , providerIntegration :: Maybe ProviderIntegrationState
  , currentStreamId :: Maybe String  -- Track active stream for cancellation
  }

-- | Component actions
data Action
  = Initialize
  | EditorChanged EditorChangeEvent
  | KeyPressed String
  | AcceptSuggestion
  | DismissSuggestion
  | ToggleEnabled
  | Receive Input

-- | Component output
data Output
  = SuggestionAccepted InlineSuggestion
  | SuggestionDismissed
  | SuggestionsUpdated (Array InlineSuggestion)

-- | Component input
type Input =
  { providerStateRef :: Maybe (Ref ProviderState)
  }

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      let providerIntegrationM = case input.providerStateRef of
            Nothing -> Nothing
            Just ref -> Nothing  -- Will be initialized in Initialize action
      in
        { editorWatcher:
            { currentState: Nothing
            , pendingChanges: []
            , suggestionDebounceTimer: Nothing
            , lastSuggestionTime: 0.0
            }
        , displayState:
            { currentSuggestion: Nothing
            , alternativeIndex: 0
            , alternatives: []
            , isVisible: false
            , acceptedLength: 0
            , streamingText: ""
            , isStreaming: false
            , cursorPosition: { line: 0, column: 0 }
            }
        , isEnabled: true
        , providerIntegration: providerIntegrationM
        , currentStreamId: Nothing
        }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

-- | Actions are already defined above, remove duplicate

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state = do
  HH.div
    [ HP.class_ (H.ClassName "inline-suggestions") ]
    [ if state.isEnabled then
        renderSuggestionComponent state.displayState
      else
        HH.text ""
    , HH.div
        [ HP.class_ (H.ClassName "suggestion-controls") ]
        [ HH.button
            [ HP.class_ (H.ClassName "toggle-btn")
            , HE.onClick \_ -> ToggleEnabled
            ]
            [ HH.text (if state.isEnabled then "Disable" else "Enable") ]
        ]
    ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Provider integration will be initialized when Input is received
    -- Start watching editor
    currentState <- getCurrentEditorState
    H.modify_ \s -> s
      { editorWatcher = s.editorWatcher { currentState = currentState } }
  
  EditorChanged event -> do
    state <- H.get
    -- Update editor watcher
    newWatcherState <- handleEditorChange event state.editorWatcher
    H.modify_ _ { editorWatcher = newWatcherState }
    
    -- Request new suggestions after debounce
    delay (Milliseconds 300.0)
    requestSuggestions
  
  KeyPressed key -> do
    state <- H.get
    -- Handle suggestion-specific keys
    let newDisplayState = handleSuggestionKey key state.displayState
    H.modify_ _ { displayState = newDisplayState }
    
    -- If Tab pressed, accept suggestion
    if key == "Tab" then
      handleAction AcceptSuggestion
    else if key == "Escape" then
      handleAction DismissSuggestion
    else
      pure unit
  
  AcceptSuggestion -> do
    state <- H.get
    let acceptance = acceptSuggestion state.displayState
    case acceptance of
      AcceptFull suggestion -> do
        H.raise (SuggestionAccepted suggestion)
        H.modify_ \s -> s
          { displayState = s.displayState
              { currentSuggestion = Nothing
              , isVisible = false
              }
          }
      AcceptPartial suggestion length -> do
        H.raise (SuggestionAccepted suggestion)
        H.modify_ \s -> s
          { displayState = s.displayState
              { acceptedLength = length
              }
          }
      NoSuggestion -> pure unit
  
  DismissSuggestion -> do
    H.modify_ \s -> s
      { displayState = s.displayState
          { currentSuggestion = Nothing
          , isVisible = false
          }
      }
    H.raise SuggestionDismissed
  
  ToggleEnabled -> do
    H.modify_ \s -> s { isEnabled = not s.isEnabled }
  
  Receive input -> do
    -- Initialize provider integration when input is received
    case input.providerStateRef of
      Nothing -> pure unit
      Just ref -> do
        providerIntegration <- H.lift $ initProviderIntegration ref
        H.modify_ \s -> s { providerIntegration = Just providerIntegration }

-- | Request suggestions for current editor state
requestSuggestions :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
requestSuggestions = do
  state <- H.get
  case state.editorWatcher.currentState of
    Nothing -> pure unit
    Just editorState -> do
      -- Cancel any existing stream
      case state.currentStreamId of
        Nothing -> pure unit
        Just streamId -> do
          liftEffect $ cancelStream streamId
      
      let request =
            { editorState: editorState
            , maxSuggestions: 3
            , timeout: 2000.0
            }
      
      -- Create a Ref to accumulate streaming text (shared between streaming and component)
      streamingTextRef <- liftEffect $ Ref.new ""
      
      -- Start streaming suggestions with chunk-by-chunk updates
      -- The callback updates the Ref, and we'll poll it or use an effect to read updates
      streamIdM <- H.lift $ streamSuggestionChunks state.providerIntegration request \chunk -> do
        -- Accumulate chunk in Ref (this runs in Aff, can't directly update Halogen state)
        liftEffect do
          current <- Ref.read streamingTextRef
          Ref.write (current <> chunk) streamingTextRef
      
      -- Store stream ID for cancellation
      case streamIdM of
        Nothing -> pure unit
        Just streamId -> do
          H.modify_ \s -> s { currentStreamId = Just streamId }
          
          -- Poll the Ref to update display state (simplified - in production would use proper event system)
          _ <- H.fork $ pollStreamingUpdates streamingTextRef streamId
      
      -- Also get full response using ProviderIntegration for alternatives
      response <- generateIntelligentCompletions state.providerIntegration request
      
      -- Update display state with first suggestion and alternatives
      case Array.head response.suggestions of
        Nothing -> pure unit
        Just firstSuggestion -> do
          H.modify_ \s -> s
            { displayState = s.displayState
                { currentSuggestion = Just firstSuggestion
                , alternatives = response.suggestions
                , isVisible = true
                , cursorPosition = editorState.cursorPosition
                }
            }
          H.raise (SuggestionsUpdated response.suggestions)
      
      -- Mark streaming as complete after a short delay (or when stream completes)
      delay (Milliseconds 100.0)
      H.modify_ \s -> s
        { displayState = completeStreaming s.displayState
        , currentStreamId = Nothing
        }

-- | Poll streaming updates from Ref and update display state
pollStreamingUpdates :: forall m. MonadAff m => Ref String -> String -> H.HalogenM State Action () Output m Unit
pollStreamingUpdates textRef streamId = do
  -- Check if stream is still active
  state <- H.get
  case state.currentStreamId of
    Nothing -> pure unit  -- Stream cancelled
    Just activeStreamId -> do
      if activeStreamId == streamId then
        do
          -- Read accumulated text
          currentText <- liftEffect $ Ref.read textRef
          
          -- Only update if text has changed
          state <- H.get
          if state.displayState.streamingText /= currentText then
            H.modify_ \s -> s
              { displayState = updateStreamingText s.displayState currentText
              }
          else
            pure unit
          
          -- Continue polling
          delay (Milliseconds 50.0)
          pollStreamingUpdates textRef streamId
      else
        pure unit  -- Different stream active

-- | Import streaming functions
import Sidepanel.Components.InlineSuggestions.StreamingEngine (streamSuggestionChunks, cancelStream)
import Data.Maybe (Maybe(..))
