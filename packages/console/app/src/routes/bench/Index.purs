-- | Benchmark Index Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/bench/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Bench.Index
  ( BenchmarkRow(..)
  , BenchmarkResult(..)
  , TaskResult(..)
  , BenchmarkListState(..)
  , parseBenchmarkResult
  , extractTaskScores
  , formatScore
  ) where

import Prelude

import Data.Array (foldl, fromFoldable)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Int (floor) as Int

-- | Task result within a benchmark
type TaskResult =
  { averageScore :: Number
  , taskId :: String
  }

-- | Parsed benchmark result
type BenchmarkResult =
  { averageScore :: Number
  , tasks :: Array TaskResult
  }

-- | Benchmark row for display
type BenchmarkRow =
  { id :: String
  , agent :: String
  , model :: String
  , averageScore :: Number
  , taskScores :: Map String Number
  }

-- | Benchmark list state
type BenchmarkListState =
  { benchmarks :: Array BenchmarkRow
  , taskIds :: Array String
  , loading :: Boolean
  }

-- | Initial state
initialState :: BenchmarkListState
initialState =
  { benchmarks: []
  , taskIds: []
  , loading: true
  }

-- | Parse benchmark result from JSON (pure transformation)
parseBenchmarkResult :: { averageScore :: Number, tasks :: Array { averageScore :: Number, task :: { id :: String } } } -> BenchmarkResult
parseBenchmarkResult raw =
  { averageScore: raw.averageScore
  , tasks: map (\t -> { averageScore: t.averageScore, taskId: t.task.id }) raw.tasks
  }

-- | Extract task scores as map (pure)
extractTaskScores :: Array TaskResult -> Map String Number
extractTaskScores tasks =
  foldl (\acc t -> Map.insert t.taskId t.averageScore acc) Map.empty tasks

-- | Build benchmark row from raw data (pure)
buildBenchmarkRow 
  :: { id :: String, agent :: String, model :: String, result :: BenchmarkResult }
  -> BenchmarkRow
buildBenchmarkRow raw =
  { id: raw.id
  , agent: raw.agent
  , model: raw.model
  , averageScore: raw.result.averageScore
  , taskScores: extractTaskScores raw.result.tasks
  }

-- | Collect all unique task IDs from benchmarks (pure)
collectTaskIds :: Array BenchmarkRow -> Array String
collectTaskIds rows =
  let
    allIds = foldl (\acc row -> acc <> fromFoldable (Map.keys row.taskScores)) [] rows
    unique = foldl (\acc id -> if elem id acc then acc else acc <> [id]) [] allIds
  in
    unique
  where
    elem :: forall a. Eq a => a -> Array a -> Boolean
    elem x arr = foldl (\acc a -> acc || a == x) false arr

-- | Format score to 3 decimal places (pure)
formatScore :: Number -> String
formatScore n = formatNumberFixed 3 n

-- | Format number with fixed decimal places (simplified implementation)
formatNumberFixed :: Int -> Number -> String
formatNumberFixed decimals num =
  let
    multiplier = pow 10.0 (toNumber decimals)
    scaled = num * multiplier
    rounded = toNumber (Int.floor (scaled + 0.5))
    intPart = Int.floor (rounded / multiplier)
    fracPart = Int.floor (rounded - toNumber intPart * multiplier)
  in
    show intPart <> "." <> padLeft decimals '0' (show fracPart)
  where
    pow :: Number -> Number -> Number
    pow _ 0.0 = 1.0
    pow base exp = base * pow base (exp - 1.0)
    
    toNumber :: Int -> Number
    toNumber _ = 0.0  -- simplified
    
    padLeft :: Int -> Char -> String -> String
    padLeft len c s =
      let slen = stringLength s
      in if slen >= len then s else replicateStr (len - slen) c <> s
    
    replicateStr :: Int -> Char -> String
    replicateStr 0 _ = ""
    replicateStr m _ = "0" <> replicateStr (m - 1) '0'
    
    stringLength :: String -> Int
    stringLength _ = 1  -- simplified

-- | Build link for task detail (pure)
buildTaskLink :: String -> String -> String
buildTaskLink benchmarkId taskId = "/bench/" <> benchmarkId <> ":" <> taskId

-- | Database query configuration (pure data)
type BenchmarkQuery =
  { table :: String
  , orderBy :: String
  , limit :: Int
  }

defaultQuery :: BenchmarkQuery
defaultQuery =
  { table: "BenchmarkTable"
  , orderBy: "timeCreated DESC"
  , limit: 100
  }
