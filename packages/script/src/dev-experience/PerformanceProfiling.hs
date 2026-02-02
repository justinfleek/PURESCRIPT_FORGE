{-# LANGUAGE OverloadedStrings #-}
-- Phase 7: Performance Profiling
module PerformanceProfiling where

import qualified Data.Text as T
import qualified System.CPUTime as CPU
import qualified System.Mem as Mem
import qualified GHC.Stats as Stats
import qualified Data.Map.Strict as Map
import Parser (PSModule(..), parseModule)
import TypeChecker (typeCheckModule)
import Cpp23Generator (generateCpp23Header, generateCpp23Impl)

-- | Performance profiler
data Profiler = Profiler
  { profileData :: Map.Map T.Text ProfileEntry
  , profileEnabled :: Bool
  }

data ProfileEntry = ProfileEntry
  { entryName :: T.Text
  , entryDuration :: Double  -- microseconds
  , entryCallCount :: Int
  , entryMemoryUsage :: Int  -- bytes
  , entryMaxMemory :: Int
  }

-- | Initialize profiler
initProfiler :: Bool -> IO Profiler
initProfiler enabled = do
  when enabled $ Mem.performGC
  return Profiler { profileData = Map.empty, profileEnabled = enabled }

-- | Profile operation
profileOperation :: Profiler -> T.Text -> IO a -> IO (a, Profiler)
profileOperation profiler name operation
  | not (profileEnabled profiler) = do
      result <- operation
      return (result, profiler)
  | otherwise = do
      -- Force GC before measurement
      Mem.performGC
      
      -- Get initial memory
      statsBefore <- Stats.getRTSStats
      let memBefore = Stats.allocated_bytes statsBefore
      
      -- Measure CPU time
      startTime <- CPU.getCPUTime
      result <- operation
      endTime <- CPU.getCPUTime
      
      -- Get final memory
      Mem.performGC
      statsAfter <- Stats.getRTSStats
      let memAfter = Stats.allocated_bytes statsAfter
      
      let duration = fromIntegral (endTime - startTime) / 1000000.0  -- Convert to microseconds
          memoryDelta = fromIntegral (memAfter - memBefore)
          maxMemory = fromIntegral (Stats.max_live_bytes statsAfter)
          
          entry = ProfileEntry
            { entryName = name
            , entryDuration = duration
            , entryCallCount = 1
            , entryMemoryUsage = memoryDelta
            , entryMaxMemory = maxMemory
            }
          updated = Map.insertWith mergeEntry name entry (profileData profiler)
      
      return (result, profiler { profileData = updated })

-- | Merge profile entries
mergeEntry :: ProfileEntry -> ProfileEntry -> ProfileEntry
mergeEntry old new = ProfileEntry
  { entryName = entryName old
  , entryDuration = entryDuration old + entryDuration new
  , entryCallCount = entryCallCount old + entryCallCount new
  , entryMemoryUsage = max (entryMemoryUsage old) (entryMemoryUsage new)
  , entryMaxMemory = max (entryMaxMemory old) (entryMaxMemory new)
  }

-- | Generate profile report
generateProfileReport :: Profiler -> T.Text
generateProfileReport profiler =
  let entries = Map.elems (profileData profiler)
      sorted = reverse (sortByDuration entries)
      report = T.unlines $ map formatEntry sorted
      totalTime = sum (map entryDuration entries)
      totalCalls = sum (map entryCallCount entries)
      header = "Performance Profile Report\n" <> T.replicate 50 "=" <> "\n\n" <>
               "Total Operations: " <> T.pack (show totalCalls) <> "\n" <>
               "Total Time: " <> T.pack (show totalTime) <> " μs\n" <>
               "Average Time: " <> T.pack (show (if totalCalls > 0 then totalTime / fromIntegral totalCalls else 0)) <> " μs\n\n"
  in header <> report

-- | Format profile entry
formatEntry :: ProfileEntry -> T.Text
formatEntry entry =
  let avgDuration = entryDuration entry / fromIntegral (entryCallCount entry)
      memoryMB = fromIntegral (entryMemoryUsage entry) / 1024.0 / 1024.0
      maxMemoryMB = fromIntegral (entryMaxMemory entry) / 1024.0 / 1024.0
  in entryName entry <> ":\n" <>
     "  Calls: " <> T.pack (show (entryCallCount entry)) <> "\n" <>
     "  Total: " <> T.pack (show (entryDuration entry)) <> " μs\n" <>
     "  Average: " <> T.pack (show avgDuration) <> " μs\n" <>
     "  Memory Delta: " <> T.pack (show memoryMB) <> " MB\n" <>
     "  Max Memory: " <> T.pack (show maxMemoryMB) <> " MB\n"

-- | Sort by duration
sortByDuration :: [ProfileEntry] -> [ProfileEntry]
sortByDuration = sortOn entryDuration

-- | Sort on key
sortOn :: Ord b => (a -> b) -> [a] -> [a]
sortOn f = sortBy (\x y -> compare (f x) (f y))

sortBy :: (a -> a -> Ordering) -> [a] -> [a]
sortBy _ [] = []
sortBy cmp (x:xs) = insertBy cmp x (sortBy cmp xs)

insertBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertBy _ x [] = [x]
insertBy cmp x (y:ys) =
  case cmp x y of
    GT -> y : insertBy cmp x ys
    _ -> x : y : ys

when :: Bool -> IO () -> IO ()
when True action = action
when False _ = return ()
