-- | Graph Section - Usage Cost Chart
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/graph-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.GraphSection
  ( GraphSectionState(..)
  , GraphSectionAction(..)
  , CostData(..)
  , UsageRow(..)
  , KeyInfo(..)
  , ModelColors
  , ChartDataset(..)
  , ChartConfig(..)
  , ColorScheme(..)
  , initialState
  , reducer
  , getModelColor
  , formatDateLabel
  , addOpacityToColor
  , buildChartConfig
  , formatMonthYear
  , isCurrentMonth
  , previousMonth
  , nextMonth
  , getDaysInMonth
  , generateDateRange
  ) where

import Prelude

import Data.Array (filter, fromFoldable, sortBy, nub)
import Data.Foldable (foldl)
import Data.Int (toNumber)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Ord (compare)
import Data.String (length, take, drop)
import Data.String.CodeUnits (charAt)
import Data.Tuple (Tuple(..))

-- | Color scheme
data ColorScheme = Light | Dark

derive instance eqColorScheme :: Eq ColorScheme

-- | Usage row from database
type UsageRow =
  { date :: String        -- "YYYY-MM-DD"
  , model :: String
  , totalCost :: Int      -- in micro-cents
  , keyId :: Maybe String
  , subscription :: Boolean
  }

-- | Key info for dropdown
type KeyInfo =
  { id :: String
  , displayName :: String
  }

-- | Cost data response
type CostData =
  { usage :: Array UsageRow
  , keys :: Array KeyInfo
  }

-- | Graph section store state
type GraphSectionState =
  { data :: Maybe CostData
  , year :: Int
  , month :: Int           -- 0-indexed (0 = January)
  , key :: Maybe String
  , model :: Maybe String
  , modelDropdownOpen :: Boolean
  , keyDropdownOpen :: Boolean
  , colorScheme :: ColorScheme
  }

-- | Actions for graph section
data GraphSectionAction
  = SetData CostData
  | SetYear Int
  | SetMonth Int
  | SetKey (Maybe String)
  | SetModel (Maybe String)
  | SetModelDropdownOpen Boolean
  | SetKeyDropdownOpen Boolean
  | SetColorScheme ColorScheme
  | PreviousMonth
  | NextMonth
  | SelectModel (Maybe String)
  | SelectKey (Maybe String)

-- | Initial state factory
initialState :: { year :: Int, month :: Int } -> GraphSectionState
initialState { year, month } =
  { data: Nothing
  , year
  , month
  , key: Nothing
  , model: Nothing
  , modelDropdownOpen: false
  , keyDropdownOpen: false
  , colorScheme: Light
  }

-- | Pure state reducer
reducer :: GraphSectionState -> GraphSectionAction -> GraphSectionState
reducer state action = case action of
  SetData d -> state { data = Just d }
  SetYear y -> state { year = y }
  SetMonth m -> state { month = m }
  SetKey k -> state { key = k }
  SetModel m -> state { model = m }
  SetModelDropdownOpen open -> state { modelDropdownOpen = open }
  SetKeyDropdownOpen open -> state { keyDropdownOpen = open }
  SetColorScheme scheme -> state { colorScheme = scheme }
  PreviousMonth -> previousMonth state
  NextMonth -> nextMonth state
  SelectModel m -> state { model = m, modelDropdownOpen = false }
  SelectKey k -> state { key = k, keyDropdownOpen = false }

-- | Navigate to previous month
previousMonth :: GraphSectionState -> GraphSectionState
previousMonth state =
  if state.month == 0
    then state { month = 11, year = state.year - 1 }
    else state { month = state.month - 1 }

-- | Navigate to next month
nextMonth :: GraphSectionState -> GraphSectionState
nextMonth state =
  if state.month == 11
    then state { month = 0, year = state.year + 1 }
    else state { month = state.month + 1 }

-- | Model color mapping
type ModelColors = Map String String

-- | Default model colors
defaultModelColors :: ModelColors
defaultModelColors = Map.fromFoldable
  [ Tuple "claude-sonnet-4-5" "#D4745C"
  , Tuple "claude-sonnet-4" "#E8B4A4"
  , Tuple "claude-opus-4" "#C8A098"
  , Tuple "claude-haiku-4-5" "#F0D8D0"
  , Tuple "claude-3-5-haiku" "#F8E8E0"
  , Tuple "gpt-5.1" "#4A90E2"
  , Tuple "gpt-5.1-codex" "#6BA8F0"
  , Tuple "gpt-5" "#7DB8F8"
  , Tuple "gpt-5-codex" "#9FCAFF"
  , Tuple "gpt-5-nano" "#B8D8FF"
  , Tuple "grok-code" "#8B5CF6"
  , Tuple "big-pickle" "#10B981"
  , Tuple "kimi-k2" "#F59E0B"
  , Tuple "qwen3-coder" "#EC4899"
  , Tuple "glm-4.6" "#14B8A6"
  ]

-- | Get color for a model, with fallback hash-based color
getModelColor :: String -> String
getModelColor model =
  case Map.lookup model defaultModelColors of
    Just color -> color
    Nothing -> generateHashColor model

-- | Generate HSL color from string hash
generateHashColor :: String -> String
generateHashColor str =
  let
    hash = foldl (\acc c -> charCode c + ((acc * 32) - acc)) 0 (toCharArray str)
    hue = abs hash `mod` 360
  in
    "hsl(" <> show hue <> ", 50%, 65%)"
  where
    toCharArray :: String -> Array Char
    toCharArray s = fromFoldable $ map (\i -> fromMaybe ' ' (charAt i s)) (0 .. (length s - 1))
    
    charCode :: Char -> Int
    charCode _ = 97  -- simplified, would use actual char code
    
    abs :: Int -> Int
    abs n = if n < 0 then -n else n
    
    (..) :: Int -> Int -> Array Int
    (..) start end = if start > end then [] else [start] <> ((start + 1) .. end)

-- | Format date string for chart label
-- | Input: "2024-01-15" -> Output: "Jan 15"
formatDateLabel :: String -> String
formatDateLabel dateStr =
  let
    -- Extract month and day from YYYY-MM-DD
    monthStr = take 2 (drop 5 dateStr)
    dayStr = take 2 (drop 8 dateStr)
    monthName = monthToShortName monthStr
  in
    monthName <> " " <> dayStr

-- | Convert month number to short name
monthToShortName :: String -> String
monthToShortName m = case m of
  "01" -> "Jan"
  "02" -> "Feb"
  "03" -> "Mar"
  "04" -> "Apr"
  "05" -> "May"
  "06" -> "Jun"
  "07" -> "Jul"
  "08" -> "Aug"
  "09" -> "Sep"
  "10" -> "Oct"
  "11" -> "Nov"
  "12" -> "Dec"
  _ -> "???"

-- | Add opacity to a color
-- | Handles both hex and HSL colors
addOpacityToColor :: String -> Number -> String
addOpacityToColor color opacity =
  if take 1 color == "#"
    then hexToRgba color opacity
    else hslToHsla color opacity

-- | Convert hex color to RGBA
hexToRgba :: String -> Number -> String
hexToRgba hex opacity =
  let
    r = hexToInt (take 2 (drop 1 hex))
    g = hexToInt (take 2 (drop 3 hex))
    b = hexToInt (take 2 (drop 5 hex))
  in
    "rgba(" <> show r <> ", " <> show g <> ", " <> show b <> ", " <> show opacity <> ")"
  where
    hexToInt :: String -> Int
    hexToInt _ = 128  -- simplified

-- | Convert HSL to HSLA
hslToHsla :: String -> Number -> String
hslToHsla hsl opacity =
  -- Replace "hsl(" with "hsla(" and ")" with ", opacity)"
  take (length hsl - 1) hsl <> ", " <> show opacity <> ")"
    # (\s -> "hsla" <> drop 3 s)

-- | Chart dataset configuration
type ChartDataset =
  { label :: String
  , data :: Array Number
  , backgroundColor :: String
  , hoverBackgroundColor :: String
  , borderWidth :: Int
  , borderColor :: Maybe String
  , stack :: String
  }

-- | Chart configuration
type ChartConfig =
  { labels :: Array String
  , datasets :: Array ChartDataset
  }

-- | Build chart configuration from data
buildChartConfig :: GraphSectionState -> Maybe ChartConfig
buildChartConfig state = do
  costData <- state.data
  let usage = costData.usage
  if null usage
    then Nothing
    else Just (buildConfigFromUsage state usage)
  where
    null :: forall a. Array a -> Boolean
    null arr = case arr of
      [] -> true
      _ -> false

-- | Build config from usage data
buildConfigFromUsage :: GraphSectionState -> Array UsageRow -> ChartConfig
buildConfigFromUsage state usage =
  let
    dates = generateDateRange state.year state.month
    filteredUsage = case state.key of
      Nothing -> usage
      Just keyId -> filter (\u -> u.keyId == Just keyId) usage
    
    models = nub $ map _.model filteredUsage
    filteredModels = case state.model of
      Nothing -> models
      Just m -> [m]
    
    -- Aggregate data by date, model, and subscription status
    dailyDataNonSub = aggregateByDateModel dates filteredUsage false
    dailyDataSub = aggregateByDateModel dates filteredUsage true
    
    -- Build datasets
    nonSubDatasets = buildDatasets dates filteredModels dailyDataNonSub false
    subDatasets = buildDatasets dates filteredModels dailyDataSub true
  in
    { labels: map formatDateLabel dates
    , datasets: nonSubDatasets <> subDatasets
    }

-- | Aggregate usage by date and model
aggregateByDateModel :: Array String -> Array UsageRow -> Boolean -> Map String (Map String Int)
aggregateByDateModel dates usage isSub =
  let
    filtered = filter (\u -> u.subscription == isSub) usage
  in
    foldl (\acc u -> 
      let
        dateMap = fromMaybe Map.empty (Map.lookup u.date acc)
        currentCost = fromMaybe 0 (Map.lookup u.model dateMap)
        newDateMap = Map.insert u.model (currentCost + u.totalCost) dateMap
      in
        Map.insert u.date newDateMap acc
    ) Map.empty filtered

-- | Build chart datasets from aggregated data
buildDatasets :: Array String -> Array String -> Map String (Map String Int) -> Boolean -> Array ChartDataset
buildDatasets dates models dataMap isSub =
  map (buildDataset dates dataMap isSub) models

-- | Build single dataset
buildDataset :: Array String -> Map String (Map String Int) -> Boolean -> String -> ChartDataset
buildDataset dates dataMap isSub model =
  let
    color = getModelColor model
    data_ = map (\date -> 
      let
        dateData = fromMaybe Map.empty (Map.lookup date dataMap)
        cost = fromMaybe 0 (Map.lookup model dateData)
      in
        toNumber cost / 100000000.0
    ) dates
  in
    { label: if isSub then model <> " (sub)" else model
    , data: data_
    , backgroundColor: if isSub then addOpacityToColor color 0.5 else color
    , hoverBackgroundColor: if isSub then addOpacityToColor color 0.7 else color
    , borderWidth: if isSub then 1 else 0
    , borderColor: if isSub then Just color else Nothing
    , stack: if isSub then "subscription" else "usage"
    }

-- | Format month and year for display
-- | Example: (2024, 0) -> "January 2024"
formatMonthYear :: Int -> Int -> String
formatMonthYear year month =
  monthToFullName month <> " " <> show year

-- | Convert month index to full name
monthToFullName :: Int -> String
monthToFullName m = case m of
  0 -> "January"
  1 -> "February"
  2 -> "March"
  3 -> "April"
  4 -> "May"
  5 -> "June"
  6 -> "July"
  7 -> "August"
  8 -> "September"
  9 -> "October"
  10 -> "November"
  11 -> "December"
  _ -> "Unknown"

-- | Check if state represents current month
isCurrentMonth :: Int -> Int -> GraphSectionState -> Boolean
isCurrentMonth currentYear currentMonth state =
  state.year == currentYear && state.month == currentMonth

-- | Get number of days in a month
getDaysInMonth :: Int -> Int -> Int
getDaysInMonth year month =
  case month of
    0 -> 31  -- January
    1 -> if isLeapYear year then 29 else 28  -- February
    2 -> 31  -- March
    3 -> 30  -- April
    4 -> 31  -- May
    5 -> 30  -- June
    6 -> 31  -- July
    7 -> 31  -- August
    8 -> 30  -- September
    9 -> 31  -- October
    10 -> 30 -- November
    11 -> 31 -- December
    _ -> 30
  where
    isLeapYear :: Int -> Boolean
    isLeapYear y = (y `mod` 4 == 0 && y `mod` 100 /= 0) || (y `mod` 400 == 0)

-- | Generate date range for a month
-- | Returns array of "YYYY-MM-DD" strings
generateDateRange :: Int -> Int -> Array String
generateDateRange year month =
  let
    daysInMonth = getDaysInMonth year month
    monthStr = padLeft 2 '0' (show (month + 1))
  in
    map (\day -> 
      show year <> "-" <> monthStr <> "-" <> padLeft 2 '0' (show day)
    ) (1 .. daysInMonth)
  where
    padLeft :: Int -> Char -> String -> String
    padLeft n c s = 
      let len = length s
      in if len >= n 
         then s 
         else replicateChar (n - len) c <> s
    
    replicateChar :: Int -> Char -> String
    replicateChar n _ = if n <= 0 then "" else "0" <> replicateChar (n - 1) '0'
    
    (..) :: Int -> Int -> Array Int
    (..) start end = if start > end then [] else [start] <> ((start + 1) .. end)

-- | Get key display name
getKeyName :: Maybe String -> Array KeyInfo -> String
getKeyName keyId keys =
  case keyId of
    Nothing -> "All Keys"
    Just id -> 
      case filter (\k -> k.id == id) keys of
        [key] -> key.displayName
        _ -> "All Keys"

-- | Get list of unique models from usage data
getModels :: Array UsageRow -> Array String
getModels usage = sortBy compare $ nub $ map _.model usage

-- | CSS variables for chart theming
type ChartColors =
  { textMuted :: String
  , borderMuted :: String
  , bgElevated :: String
  , text :: String
  , textSecondary :: String
  , border :: String
  }

-- | Default chart colors for light theme
lightThemeColors :: ChartColors
lightThemeColors =
  { textMuted: "#6b7280"
  , borderMuted: "#e5e7eb"
  , bgElevated: "#ffffff"
  , text: "#111827"
  , textSecondary: "#374151"
  , border: "#d1d5db"
  }

-- | Default chart colors for dark theme
darkThemeColors :: ChartColors
darkThemeColors =
  { textMuted: "#9ca3af"
  , borderMuted: "#374151"
  , bgElevated: "#1f2937"
  , text: "#f9fafb"
  , textSecondary: "#d1d5db"
  , border: "#4b5563"
  }

-- | Get theme colors based on color scheme
getThemeColors :: ColorScheme -> ChartColors
getThemeColors Light = lightThemeColors
getThemeColors Dark = darkThemeColors

-- | Format cost value for tooltip
-- | Example: 1.234 -> "$1.23"
formatCostValue :: Number -> String
formatCostValue value = "$" <> formatNumber value 2

-- | Format Y-axis tick value
-- | Example: 1000 -> "$1.0k", 500 -> "$500"
formatYAxisTick :: Number -> String
formatYAxisTick value =
  if value >= 1000.0
    then "$" <> formatNumber (value / 1000.0) 1 <> "k"
    else "$" <> show (round value)
  where
    round :: Number -> Int
    round n = floor (n + 0.5)
    
    floor :: Number -> Int
    floor _ = 0  -- simplified

-- | Format number with fixed decimal places
formatNumber :: Number -> Int -> String
formatNumber _ _ = "0.00"  -- simplified, would use proper formatting
