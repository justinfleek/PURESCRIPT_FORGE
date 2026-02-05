{-|
Module      : Sidepanel.Components.Editor.RectangularSelection
Description : Rectangular (column-based) text selection
Implements rectangular selection for column-based text operations.
-}
module Sidepanel.Components.Editor.RectangularSelection where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Sidepanel.Components.Editor.RectangularSelectionTypes
  ( RectangularSelection
  , Position
  , Rectangle
  , RectangleOperation(..)
  )

-- | Create rectangular selection
createRectangularSelection :: Position -> Position -> Array String -> RectangularSelection
createRectangularSelection start end lines =
  let normalizedStart = normalizePosition start end true
      normalizedEnd = normalizePosition start end false
      rectangle = extractRectangle lines normalizedStart normalizedEnd
  in
    { start: normalizedStart
    , end: normalizedEnd
    , rectangle: rectangle
    , isActive: true
    }

-- | Normalize position (ensure start < end)
normalizePosition :: Position -> Position -> Boolean -> Position
normalizePosition pos1 pos2 isStart =
  if pos1.line < pos2.line || (pos1.line == pos2.line && pos1.column <= pos2.column) then
    if isStart then pos1 else pos2
  else
    if isStart then pos2 else pos1

-- | Extract rectangle from lines
extractRectangle :: Array String -> Position -> Position -> Rectangle
extractRectangle lines start end =
  let startLine = start.line
      endLine = end.line
      startCol = start.column
      endCol = end.column
      minCol = if startCol < endCol then startCol else endCol
      maxCol = if startCol > endCol then startCol else endCol
      rectangleLines = Array.mapMaybe (\idx ->
        case Array.index lines idx of
          Nothing -> Nothing
          Just line ->
            let lineLength = String.length line
                extractStart = if minCol < lineLength then minCol else lineLength
                extractEnd = if maxCol < lineLength then maxCol else lineLength
                extracted = if extractStart < extractEnd then
                      String.substring extractStart extractEnd line
                    else
                      ""
            in
              Just extracted
      ) (Array.range startLine endLine)
  in
    { start: start
    , end: end
    , lines: rectangleLines
    }

-- | Apply rectangle operation
applyRectangleOperation :: RectangularSelection -> RectangleOperation -> Array String -> Array String
applyRectangleOperation selection operation lines = case operation of
  CopyRectangle -> lines  -- Would copy to clipboard
  KillRectangle -> killRectangle selection lines
  YankRectangle text -> yankRectangle selection text lines
  OpenRectangle -> openRectangle selection lines
  StringRectangle text -> stringRectangle selection text lines

-- | Kill rectangle (delete)
killRectangle :: RectangularSelection -> Array String -> Array String
killRectangle selection lines =
  let start = selection.start
      end = selection.end
      minCol = if start.column < end.column then start.column else end.column
      maxCol = if start.column > end.column then start.column else end.column
  in
    Array.mapWithIndex (\idx line ->
      if idx >= start.line && idx <= end.line then
        let lineLength = String.length line
            before = if minCol < lineLength then String.take minCol line else line
            after = if maxCol < lineLength then String.drop maxCol line else ""
        in
          before <> after
      else
        line
    ) lines

-- | Yank rectangle (insert)
yankRectangle :: RectangularSelection -> String -> Array String -> Array String
yankRectangle selection text lines =
  let start = selection.start
      end = selection.end
      rectangleLines = String.split (String.Pattern "\n") text
      minCol = if start.column < end.column then start.column else end.column
  in
    Array.mapWithIndex (\idx line ->
      if idx >= start.line && idx <= end.line then
        let lineLength = String.length line
            before = if minCol < lineLength then String.take minCol line else line
            after = if minCol < lineLength then String.drop minCol line else ""
            insertLine = fromMaybe "" (Array.index rectangleLines (idx - start.line))
        in
          before <> insertLine <> after
      else
        line
    ) lines

-- | Open rectangle (insert spaces)
openRectangle :: RectangularSelection -> Array String -> Array String
openRectangle selection lines =
  let start = selection.start
      end = selection.end
      minCol = if start.column < end.column then start.column else end.column
      maxCol = if start.column > end.column then start.column else end.column
      width = maxCol - minCol
      spaces = String.repeat width " "
  in
    Array.mapWithIndex (\idx line ->
      if idx >= start.line && idx <= end.line then
        let lineLength = String.length line
            before = if minCol < lineLength then String.take minCol line else line
            after = if minCol < lineLength then String.drop minCol line else ""
        in
          before <> spaces <> after
      else
        line
    ) lines

-- | String rectangle (replace with text)
stringRectangle :: RectangularSelection -> String -> Array String -> Array String
stringRectangle selection text lines =
  let start = selection.start
      end = selection.end
      rectangleLines = String.split (String.Pattern "\n") text
      minCol = if start.column < end.column then start.column else end.column
      maxCol = if start.column > end.column then start.column else end.column
  in
    Array.mapWithIndex (\idx line ->
      if idx >= start.line && idx <= end.line then
        let lineLength = String.length line
            before = if minCol < lineLength then String.take minCol line else line
            after = if maxCol < lineLength then String.drop maxCol line else ""
            replaceText = fromMaybe "" (Array.index rectangleLines (idx - start.line))
        in
          before <> replaceText <> after
      else
        line
    ) lines

-- | Get rectangle text
getRectangleText :: RectangularSelection -> String
getRectangleText selection =
  String.joinWith "\n" selection.rectangle.lines
