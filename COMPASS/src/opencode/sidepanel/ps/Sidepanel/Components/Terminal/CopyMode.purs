{-|
Module      : Sidepanel.Components.Terminal.CopyMode
Description : Tmux-style copy mode for terminal scrollback
Implements copy mode for navigating scrollback buffer, selecting text, and copying.
-}
module Sidepanel.Components.Terminal.CopyMode where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.Terminal.CopyModeTypes
  ( CopyModeState
  , Selection
  , SearchDirection(..)
  , CopyModeAction(..)
  )

-- | Enter copy mode
enterCopyMode :: Array String -> CopyModeState
enterCopyMode scrollbackLines =
  { lines: scrollbackLines
  , currentLine: Array.length scrollbackLines - 1  -- Start at bottom
  , currentColumn: 0
  , selectionStart: Nothing
  , selectionEnd: Nothing
  , searchQuery: ""
  , searchResults: []
  , currentSearchIndex: 0
  , isActive: true
  }

-- | Exit copy mode
exitCopyMode :: CopyModeState -> CopyModeState
exitCopyMode state = state { isActive = false }

-- | Handle copy mode action
handleCopyModeAction :: CopyModeState -> CopyModeAction -> CopyModeState
handleCopyModeAction state action = case action of
  MoveUp -> moveCursor state 0 (-1)
  MoveDown -> moveCursor state 0 1
  MoveLeft -> moveCursor state (-1) 0
  MoveRight -> moveCursor state 1 0
  MoveToStartOfLine -> moveToStartOfLine state
  MoveToEndOfLine -> moveToEndOfLine state
  MoveToTop -> moveToTop state
  MoveToBottom -> moveToBottom state
  PageUp -> pageUp state
  PageDown -> pageDown state
  StartSelection -> startSelection state
  EndSelection -> endSelection state
  CopySelection -> state  -- Would copy to clipboard
  SearchForward query -> searchForward state query
  SearchBackward query -> searchBackward state query
  NextSearchResult -> nextSearchResult state
  PreviousSearchResult -> previousSearchResult state
  Exit -> exitCopyMode state

-- | Move cursor
moveCursor :: CopyModeState -> Int -> Int -> CopyModeState
moveCursor state colDelta lineDelta =
  let newLine = clamp 0 (Array.length state.lines - 1) (state.currentLine + lineDelta)
      currentLineText = fromMaybe "" (Array.index state.lines newLine)
      maxCol = String.length currentLineText
      newCol = clamp 0 maxCol (state.currentColumn + colDelta)
  in
    state { currentLine = newLine, currentColumn = newCol }

-- | Move to start of line
moveToStartOfLine :: CopyModeState -> CopyModeState
moveToStartOfLine state = state { currentColumn = 0 }

-- | Move to end of line
moveToEndOfLine :: CopyModeState -> CopyModeState
moveToEndOfLine state =
  let currentLineText = fromMaybe "" (Array.index state.lines state.currentLine)
  in
    state { currentColumn = String.length currentLineText }

-- | Move to top
moveToTop :: CopyModeState -> CopyModeState
moveToTop state = state { currentLine = 0, currentColumn = 0 }

-- | Move to bottom
moveToBottom :: CopyModeState -> CopyModeState
moveToBottom state =
  let lastLine = Array.length state.lines - 1
      lastLineText = fromMaybe "" (Array.index state.lines lastLine)
  in
    state { currentLine = lastLine, currentColumn = String.length lastLineText }

-- | Page up
pageUp :: CopyModeState -> CopyModeState
pageUp state =
  let pageSize = 20
      newLine = clamp 0 (Array.length state.lines - 1) (state.currentLine - pageSize)
  in
    state { currentLine = newLine }

-- | Page down
pageDown :: CopyModeState -> CopyModeState
pageDown state =
  let pageSize = 20
      newLine = clamp 0 (Array.length state.lines - 1) (state.currentLine + pageSize)
  in
    state { currentLine = newLine }

-- | Start selection
startSelection :: CopyModeState -> CopyModeState
startSelection state =
  state { selectionStart = Just { line: state.currentLine, column: state.currentColumn } }

-- | End selection
endSelection :: CopyModeState -> CopyModeState
endSelection state =
  state { selectionEnd = Just { line: state.currentLine, column: state.currentColumn } }

-- | Search forward
searchForward :: CopyModeState -> String -> CopyModeState
searchForward state query =
  let results = findSearchResults state.lines query state.currentLine Forward
  in
    state
      { searchQuery = query
      , searchResults = results
      , currentSearchIndex = 0
      }

-- | Search backward
searchBackward :: CopyModeState -> String -> CopyModeState
searchBackward state query =
  let results = findSearchResults state.lines query state.currentLine Backward
  in
    state
      { searchQuery = query
      , searchResults = results
      , currentSearchIndex = Array.length results - 1
      }

-- | Find search results
findSearchResults :: Array String -> String -> Int -> SearchDirection -> Array { line :: Int, column :: Int }
findSearchResults lines query startLine direction =
  let searchLines = case direction of
        Forward -> Array.drop startLine lines
        Backward -> Array.take (startLine + 1) lines
      results = Array.concatMapWithIndex (\idx line ->
        let matches = findAllMatches line query
            lineNum = case direction of
              Forward -> startLine + idx
              Backward -> idx
        in
          Array.map (\col -> { line: lineNum, column: col }) matches
      ) searchLines
  in
    results

-- | Find all matches in string
findAllMatches :: String -> String -> Array Int
findAllMatches text pattern =
  if String.null pattern then
    []
  else
    findAllMatchesHelper text pattern 0 []

-- | Helper for finding matches
findAllMatchesHelper :: String -> String -> Int -> Array Int -> Array Int
findAllMatchesHelper text pattern startPos acc =
  case String.indexOf (String.Pattern pattern) (String.drop startPos text) of
    Nothing -> acc
    Just idx ->
      let absolutePos = startPos + idx
          nextPos = absolutePos + String.length pattern
      in
        if nextPos >= String.length text then
          acc <> [absolutePos]
        else
          findAllMatchesHelper text pattern nextPos (acc <> [absolutePos])

-- | Next search result
nextSearchResult :: CopyModeState -> CopyModeState
nextSearchResult state =
  if Array.length state.searchResults == 0 then
    state
  else
    let newIndex = (state.currentSearchIndex + 1) `mod` Array.length state.searchResults
        result = Array.index state.searchResults newIndex
    in
      case result of
        Nothing -> state
        Just { line, column } -> state
          { currentLine = line
          , currentColumn = column
          , currentSearchIndex = newIndex
          }

-- | Previous search result
previousSearchResult :: CopyModeState -> CopyModeState
previousSearchResult state =
  if Array.length state.searchResults == 0 then
    state
  else
    let len = Array.length state.searchResults
        newIndex = if state.currentSearchIndex == 0 then len - 1 else state.currentSearchIndex - 1
        result = Array.index state.searchResults newIndex
    in
      case result of
        Nothing -> state
        Just { line, column } -> state
          { currentLine = line
          , currentColumn = column
          , currentSearchIndex = newIndex
          }

-- | Get selected text
getSelectedText :: CopyModeState -> Maybe String
getSelectedText state = do
  start <- state.selectionStart
  end <- state.selectionEnd
  
  -- Normalize selection
  let normalizedStart = if start.line < end.line || (start.line == end.line && start.column <= end.column) then start else end
  let normalizedEnd = if start.line < end.line || (start.line == end.line && start.column <= end.column) then end else start
  
  -- Extract text
  if normalizedStart.line == normalizedEnd.line then
    -- Single line selection
    let line = fromMaybe "" (Array.index state.lines normalizedStart.line)
        selected = String.substring normalizedStart.column normalizedEnd.column line
    in
      Just selected
  else
    -- Multi-line selection
    let firstLine = fromMaybe "" (Array.index state.lines normalizedStart.line)
        lastLine = fromMaybe "" (Array.index state.lines normalizedEnd.line)
        firstPart = String.drop normalizedStart.column firstLine
        lastPart = String.take normalizedEnd.column lastLine
        middleLines = Array.slice (normalizedStart.line + 1) normalizedEnd.line state.lines
        allParts = [firstPart] <> middleLines <> [lastPart]
    in
      Just (String.joinWith "\n" allParts)

-- | Clamp number
clamp :: Int -> Int -> Int -> Int
clamp min max value =
  if value < min then min
  else if value > max then max
  else value
