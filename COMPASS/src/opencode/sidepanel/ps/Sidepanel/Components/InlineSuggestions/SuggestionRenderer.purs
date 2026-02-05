{-|
Module      : Sidepanel.Components.InlineSuggestions.SuggestionRenderer
Description : UI rendering for inline code suggestions (ghost text)

Renders inline suggestions as ghost text in the editor, handles keyboard interactions.
-}
module Sidepanel.Components.InlineSuggestions.SuggestionRenderer where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect (Effect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( InlineSuggestion
  , Position
  , Range
  )

-- | Suggestion display state
type SuggestionDisplayState =
  { currentSuggestion :: Maybe InlineSuggestion
  , alternativeIndex :: Int  -- Which alternative is shown
  , alternatives :: Array InlineSuggestion
  , isVisible :: Boolean
  , acceptedLength :: Int  -- How many characters accepted (for partial acceptance)
  , streamingText :: String  -- Accumulated text from streaming
  , isStreaming :: Boolean  -- Whether suggestion is still streaming
  , cursorPosition :: Position  -- Current cursor position for positioning
  }

-- | Render ghost text overlay with proper positioning and styling
renderGhostText :: SuggestionDisplayState -> H.ComponentHTML Action () m
renderGhostText state = do
  case state.currentSuggestion of
    Nothing -> HH.text ""
    Just suggestion -> do
      let visibleText = getVisibleText suggestion state.acceptedLength state.streamingText
      let position = calculateSuggestionPosition state.cursorPosition suggestion.range
      let lineHeight = 20.0  -- Default line height in pixels
      let charWidth = 8.0  -- Default character width in pixels
      let topPx = position.top * lineHeight
      let leftPx = position.left * charWidth
      
      HH.div
        [ HP.class_ (H.ClassName "inline-suggestion-ghost")
        , HP.style (buildGhostTextStyle topPx leftPx state.isStreaming)
        ]
        [ renderSuggestionText visibleText state.isStreaming
        , renderSuggestionInfo state.alternatives state.alternativeIndex
        , renderAlternativeSuggestions state.alternatives state.alternativeIndex
        ]

-- | Build CSS style for ghost text
buildGhostTextStyle :: Number -> Number -> Boolean -> String
buildGhostTextStyle topPx leftPx isStreaming = do
  let baseStyle = "position: absolute; "
      <> "top: " <> show topPx <> "px; "
      <> "left: " <> show leftPx <> "px; "
      <> "color: #6a9955; "
      <> "opacity: " <> (if isStreaming then "0.5" else "0.7") <> "; "
      <> "pointer-events: none; "
      <> "font-family: 'Consolas', 'Monaco', 'Courier New', monospace; "
      <> "font-size: 14px; "
      <> "line-height: 20px; "
      <> "white-space: pre; "
      <> "z-index: 1000; "
      <> "user-select: none;"
  baseStyle

-- | Render suggestion text with proper formatting
renderSuggestionText :: String -> Boolean -> H.ComponentHTML Action () m
renderSuggestionText text isStreaming = do
  let lines = String.split (String.Pattern "\n") text
  HH.div
    [ HP.class_ (H.ClassName "suggestion-text") ]
    (Array.mapWithIndex (\index line ->
      HH.div
        [ HP.class_ (H.ClassName "suggestion-line") ]
        [ HH.text line
        , if isStreaming && index == Array.length lines - 1 then
            HH.span
              [ HP.class_ (H.ClassName "streaming-cursor")
              , HP.style "display: inline-block; width: 2px; height: 16px; background: #6a9955; margin-left: 2px; animation: blink 1s infinite;"
              ]
              []
          else
            HH.text ""
        ]
    ) lines)

-- | Render suggestion info (keyboard hints)
renderSuggestionInfo :: Array InlineSuggestion -> Int -> H.ComponentHTML Action () m
renderSuggestionInfo alternatives currentIndex = do
  if Array.length alternatives > 1 then
    HH.div
      [ HP.class_ (H.ClassName "suggestion-info")
      , HP.style "font-size: 11px; color: #858585; margin-top: 4px; padding-left: 2px;"
      ]
      [ HH.text ("Tab to accept, Esc to dismiss, ↑↓ to cycle (" <> show (currentIndex + 1) <> "/" <> show (Array.length alternatives) <> ")")
      ]
  else
    HH.div
      [ HP.class_ (H.ClassName "suggestion-info")
      , HP.style "font-size: 11px; color: #858585; margin-top: 4px; padding-left: 2px;"
      ]
      [ HH.text "Tab to accept, Esc to dismiss"
      ]

-- | Render alternative suggestions dropdown (when cycling)
renderAlternativeSuggestions :: Array InlineSuggestion -> Int -> H.ComponentHTML Action () m
renderAlternativeSuggestions alternatives currentIndex = do
  if Array.length alternatives > 1 then
    HH.div
      [ HP.class_ (H.ClassName "alternative-suggestions")
      , HP.style "position: absolute; top: 100%; left: 0; background: #1e1e1e; border: 1px solid #3e3e3e; border-radius: 4px; padding: 4px; margin-top: 4px; max-height: 200px; overflow-y: auto; z-index: 1001; display: none;"
      ]
      (Array.mapWithIndex (\index suggestion ->
        HH.div
          [ HP.class_ (H.ClassName (if index == currentIndex then "alternative-active" else "alternative"))
          , HP.style (if index == currentIndex then "background: #2a2a2a; padding: 4px; border-radius: 2px;" else "padding: 4px;")
          ]
          [ HH.text (String.take 80 suggestion.text <> (if String.length suggestion.text > 80 then "..." else ""))
          ]
      ) alternatives)
  else
    HH.text ""

-- | Get visible text (for partial acceptance and streaming)
getVisibleText :: InlineSuggestion -> Int -> String -> String
getVisibleText suggestion acceptedLength streamingText = do
  let baseText = if String.length streamingText > 0 then streamingText else suggestion.text
  String.drop acceptedLength baseText

-- | Handle keyboard input for suggestions
handleSuggestionKey :: String -> SuggestionDisplayState -> SuggestionDisplayState
handleSuggestionKey key state = case state.currentSuggestion of
  Nothing -> state
  Just suggestion -> case key of
    "Tab" -> state  -- Accept suggestion (handled by parent component)
    "Escape" -> state { isVisible = false, currentSuggestion = Nothing, streamingText = "", isStreaming = false }
    "ArrowUp" -> cycleAlternative state (-1)
    "ArrowDown" -> cycleAlternative state 1
    "Right" -> incrementAcceptedLength state  -- Accept one word/character
    _ -> state

-- | Increment accepted length (for partial acceptance)
incrementAcceptedLength :: SuggestionDisplayState -> SuggestionDisplayState
incrementAcceptedLength state = case state.currentSuggestion of
  Nothing -> state
  Just suggestion -> do
    let currentText = if String.length state.streamingText > 0 then state.streamingText else suggestion.text
    let newLength = min (state.acceptedLength + 1) (String.length currentText)
    state { acceptedLength = newLength }

-- | Cycle through alternative suggestions
cycleAlternative :: SuggestionDisplayState -> Int -> SuggestionDisplayState
cycleAlternative state direction = do
  if Array.length state.alternatives == 0 then
    state
  else do
    let newIndex = ((state.alternativeIndex + direction) + Array.length state.alternatives) `mod` Array.length state.alternatives
    let newSuggestion = Array.index state.alternatives newIndex
    case newSuggestion of
      Nothing -> state
      Just suggestion -> state
        { alternativeIndex = newIndex
        , currentSuggestion = Just suggestion
        , acceptedLength = 0  -- Reset accepted length when switching alternatives
        , streamingText = ""  -- Reset streaming text
        }

-- | Accept suggestion (full or partial)
acceptSuggestion :: SuggestionDisplayState -> SuggestionAcceptance
acceptSuggestion state = case state.currentSuggestion of
  Nothing -> NoSuggestion
  Just suggestion -> do
    let currentText = if String.length state.streamingText > 0 then state.streamingText else suggestion.text
    if state.acceptedLength == 0 || state.acceptedLength >= String.length currentText then
      AcceptFull suggestion
    else
      AcceptPartial suggestion state.acceptedLength

-- | Update streaming text (called as chunks arrive or when setting accumulated text)
updateStreamingText :: SuggestionDisplayState -> String -> SuggestionDisplayState
updateStreamingText state newText = do
  -- Replace streaming text with new accumulated text
  state { streamingText = newText, isStreaming = true }

-- | Mark streaming as complete
completeStreaming :: SuggestionDisplayState -> SuggestionDisplayState
completeStreaming state = do
  state { isStreaming = false }

-- | Suggestion acceptance result
data SuggestionAcceptance
  = AcceptFull InlineSuggestion
  | AcceptPartial InlineSuggestion Int
  | NoSuggestion

-- | Component actions
data Action
  = ShowSuggestion InlineSuggestion
  | HideSuggestion
  | AcceptCurrentSuggestion
  | CycleAlternative Int
  | PartialAccept Int
  | UpdateStreamingText String
  | CompleteStreaming

-- | Render suggestion component with proper positioning
renderSuggestionComponent :: SuggestionDisplayState -> H.ComponentHTML Action () m
renderSuggestionComponent state = do
  if state.isVisible then
    renderGhostText state
  else
    HH.text ""

-- | Calculate suggestion position in editor (pixel coordinates)
calculateSuggestionPosition :: Position -> Range -> { top :: Number, left :: Number }
calculateSuggestionPosition cursorPosition suggestionRange = do
  -- Calculate relative to cursor position
  -- For now, assume suggestion starts at cursor
  { top: Number.fromInt cursorPosition.line, left: Number.fromInt cursorPosition.column }

-- | Import Data.Int for mod
import Data.Int (mod)
import Data.Number as Number
