{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Types for spec loading
module SpecLoader.Types where

import Prelude hiding (head, tail, undefined, error)
import Data.Text (Text)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | Complete specification file
data SpecFile = SpecFile
  { specNumber :: !Int
  , specName :: !Text
  , specPath :: !FilePath
  , specContent :: !Text
  , specLineCount :: !Int
  }
  deriving (Show, Eq)

-- | All specifications indexed by number
type SpecIndex = Map Int SpecFile

-- | Specification suite
data SpecSuite = SpecSuite
  { suiteIndex :: !SpecIndex
  , suiteTotal :: !Int
  , suiteBasePath :: !FilePath
  }
  deriving (Show, Eq)

-- | Load result
data LoadResult
  = LoadSuccess SpecSuite
  | LoadFailure Text
  deriving (Show, Eq)
