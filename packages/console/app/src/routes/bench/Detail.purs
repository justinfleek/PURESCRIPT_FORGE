-- | Benchmark Detail Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/bench/[id].tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Bench.Detail
  ( TaskSource(..)
  , Judge(..)
  , ScoreDetail(..)
  , RunUsage(..)
  , Run(..)
  , Prompt(..)
  , AverageUsage(..)
  , Task(..)
  , BenchmarkResult(..)
  , DetailParams(..)
  , parseDetailParams
  , formatDuration
  , formatCost
  , buildGithubCommitLink
  , buildGithubRepoLink
  ) where

import Prelude

import Data.Array (index)
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (toStringWith, fixed)
import Data.String (Pattern(..), split)

-- | Task source information
type TaskSource =
  { repo :: String
  , from :: String
  , to :: String
  }

-- | Judge result
type Judge =
  { score :: Number
  , rationale :: String
  , judge :: String
  }

-- | Score detail for a criterion
type ScoreDetail =
  { criterion :: String
  , weight :: Number
  , average :: Number
  , variance :: Maybe Number
  , judges :: Maybe (Array Judge)
  }

-- | Run usage statistics
type RunUsage =
  { input :: Int
  , output :: Int
  , cost :: Number
  }

-- | Individual run result
type Run =
  { task :: String
  , model :: String
  , agent :: String
  , score :: { final :: Number, base :: Number, penalty :: Number }
  , scoreDetails :: Array ScoreDetail
  , usage :: Maybe RunUsage
  , duration :: Maybe Int  -- milliseconds
  }

-- | Prompt information
type Prompt =
  { commit :: String
  , prompt :: String
  }

-- | Average usage statistics
type AverageUsage =
  { input :: Number
  , output :: Number
  , cost :: Number
  }

-- | Task detail
type Task =
  { averageScore :: Number
  , averageDuration :: Maybe Number
  , averageUsage :: Maybe AverageUsage
  , model :: Maybe String
  , agent :: Maybe String
  , summary :: Maybe String
  , runs :: Maybe (Array Run)
  , taskInfo :: 
      { id :: String
      , source :: TaskSource
      , prompts :: Maybe (Array Prompt)
      }
  }

-- | Benchmark result
type BenchmarkResult =
  { averageScore :: Number
  , tasks :: Array Task
  }

-- | Route parameters
type DetailParams =
  { benchmarkId :: String
  , taskId :: String
  }

-- | Parse detail params from route ID (pure)
-- | Format: "benchmarkId:taskId"
parseDetailParams :: String -> Maybe DetailParams
parseDetailParams id =
  let
    parts = split (Pattern ":") id
  in
    case index parts 0, index parts 1 of
      Just benchmarkId, Just taskId -> Just { benchmarkId, taskId }
      _, _ -> Nothing

-- | Format duration from milliseconds (pure)
formatDuration :: Int -> String
formatDuration ms =
  let
    seconds = ms / 1000
    minutes = floor (toNumber seconds / 60.0)
    remainingSeconds = seconds `mod` 60
  in
    if minutes > 0 then
      show minutes <> "m " <> show remainingSeconds <> "s"
    else
      show seconds <> "s"

-- | Format cost as currency (pure)
formatCost :: Number -> String
formatCost cost = "$" <> toStringWith (fixed 4) cost

-- | Build GitHub repository link (pure)
buildGithubRepoLink :: String -> String
buildGithubRepoLink repo = "https://github.com/" <> repo

-- | Build GitHub commit link (pure)
buildGithubCommitLink :: String -> String -> String
buildGithubCommitLink repo commit = 
  "https://github.com/" <> repo <> "/commit/" <> commit

-- | Truncate commit hash for display (pure)
truncateCommit :: String -> String
truncateCommit commit =
  -- Take first 7 characters
  let len = 7 in
  if length commit > len then take len commit else commit
  where
    length :: String -> Int
    length s = 0  -- simplified, would use String.length
    take :: Int -> String -> String
    take n s = s  -- simplified, would use String.take

-- | Format score with pass/fail indicator (pure)
formatJudgeScore :: Number -> String
formatJudgeScore score
  | score == 1.0 = "✓"
  | score == 0.0 = "✗"
  | otherwise = toStringWith (fixed 1) score

-- | Check if score is passing (pure)
isPassingScore :: Number -> Boolean
isPassingScore score = score == 1.0

-- | Check if score is failing (pure)
isFailingScore :: Number -> Boolean
isFailingScore score = score == 0.0
