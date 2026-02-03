{-# LANGUAGE StrictData #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Main spec loader module
module SpecLoader where

import Prelude hiding (head, tail, undefined, error)
import SpecLoader.Types
import SpecLoader.Parser

-- | Load all specs
loadAllSpecs :: FilePath -> IO LoadResult
loadAllSpecs = loadSpecSuite

-- | Get spec by number
getSpec :: SpecSuite -> Int -> Maybe SpecFile
getSpec suite num = Map.lookup num (suiteIndex suite)

-- | Get all specs
getAllSpecs :: SpecSuite -> [SpecFile]
getAllSpecs suite = Map.elems (suiteIndex suite)

-- | Verify all 99 specs are present
verifySpecCount :: SpecSuite -> Bool
verifySpecCount suite = suiteTotal suite == 99
