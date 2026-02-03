-- | Benchmark Submission Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/bench/submission.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Bench.Submission
  ( SubmissionBody(..)
  , SubmissionResult(..)
  , ValidationError(..)
  , validateSubmission
  , buildInsertData
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (null, trim)

-- | Submission request body
type SubmissionBody =
  { model :: String
  , agent :: String
  , result :: String
  }

-- | Validation errors
data ValidationError
  = MissingModel
  | MissingAgent
  | MissingResult

derive instance eqValidationError :: Eq ValidationError

instance showValidationError :: Show ValidationError where
  show MissingModel = "Model is required"
  show MissingAgent = "Agent is required"
  show MissingResult = "Result is required"

-- | Submission result
data SubmissionResult
  = SubmissionSuccess
  | SubmissionError { error :: String, status :: Int }

derive instance eqSubmissionResult :: Eq SubmissionResult

instance showSubmissionResult :: Show SubmissionResult where
  show SubmissionSuccess = "SubmissionSuccess"
  show (SubmissionError r) = "(SubmissionError " <> show r.error <> ")"

-- | Validate submission body (pure)
validateSubmission :: SubmissionBody -> Either ValidationError SubmissionBody
validateSubmission body
  | null (trim body.model) = Left MissingModel
  | null (trim body.agent) = Left MissingAgent
  | null (trim body.result) = Left MissingResult
  | otherwise = Right body

-- | Insert data configuration (pure)
type BenchmarkInsert =
  { table :: String
  , model :: String
  , agent :: String
  , result :: String
  }

-- | Build insert data (pure)
buildInsertData :: SubmissionBody -> BenchmarkInsert
buildInsertData body =
  { table: "BenchmarkTable"
  , model: body.model
  , agent: body.agent
  , result: body.result
  }

-- | Success response
successResponse :: SubmissionResult
successResponse = SubmissionSuccess

-- | Error response builder
errorResponse :: ValidationError -> SubmissionResult
errorResponse err = SubmissionError { error: show err, status: 400 }
