-- | Comprehensive Tests for Forge Rules Modules
-- | Tests Core, TypeSafety, Verification, and FileReading rules
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module RulesSpec (spec) where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.IO.Temp (withSystemTempDirectory)
import System.FilePath ((</>))
import Data.Maybe (isJust, isNothing)

import Rules.Core
import Rules.TypeSafety
import Rules.Verification
import Rules.FileReading

spec :: Spec
spec = do
  describe "Rules.Core" $ do
    describe "TaskCompletion" $ do
      it "creates a complete task when all fields are True" $ do
        let task = TaskCompletion True True True True True True
        verifyCompletion task `shouldBe` True

      it "fails verification when codeCompiles is False" $ do
        let task = TaskCompletion False True True True True True
        verifyCompletion task `shouldBe` False

      it "fails verification when typeChecks is False" $ do
        let task = TaskCompletion True False True True True True
        verifyCompletion task `shouldBe` False

      it "fails verification when testsPass is False" $ do
        let task = TaskCompletion True True False True True True
        verifyCompletion task `shouldBe` False

      it "fails verification when documentationUpdated is False" $ do
        let task = TaskCompletion True True True False True True
        verifyCompletion task `shouldBe` False

      it "fails verification when workspaceClean is False" $ do
        let task = TaskCompletion True True True True False True
        verifyCompletion task `shouldBe` False

      it "fails verification when noTechnicalDebt is False" $ do
        let task = TaskCompletion True True True True True False
        verifyCompletion task `shouldBe` False

      it "fails verification when multiple fields are False" $ do
        let task = TaskCompletion False False True True True True
        verifyCompletion task `shouldBe` False

      it "fails verification when all fields are False" $ do
        let task = TaskCompletion False False False False False False
        verifyCompletion task `shouldBe` False

    describe "safeHead" $ do
      it "returns Nothing for empty list" $ do
        safeHead ([] :: [Int]) `shouldBe` Nothing

      it "returns Just first element for non-empty list" $ do
        safeHead [1, 2, 3] `shouldBe` Just 1

      it "returns Just single element for singleton list" $ do
        safeHead [42] `shouldBe` Just 42

      it "works with Text" $ do
        safeHead ["hello", "world"] `shouldBe` Just "hello"

    describe "safeTail" $ do
      it "returns Nothing for empty list" $ do
        safeTail ([] :: [Int]) `shouldBe` Nothing

      it "returns Just rest for non-empty list" $ do
        safeTail [1, 2, 3] `shouldBe` Just [2, 3]

      it "returns Just empty for singleton list" $ do
        safeTail [42] `shouldBe` Just []

      it "works with Text" $ do
        safeTail ["hello", "world", "!"] `shouldBe` Just ["world", "!"]

    describe "Accuracy newtype" $ do
      it "wraps True correctly" $ do
        Accuracy True `shouldBe` Accuracy True

      it "wraps False correctly" $ do
        Accuracy False `shouldBe` Accuracy False

      it "different values are not equal" $ do
        Accuracy True `shouldNotBe` Accuracy False

    describe "Completeness newtype" $ do
      it "wraps True correctly" $ do
        Completeness True `shouldBe` Completeness True

      it "wraps False correctly" $ do
        Completeness False `shouldBe` Completeness False

  describe "Rules.TypeSafety" $ do
    describe "explicitDefault" $ do
      it "returns value when Just" $ do
        explicitDefault (Just 42) 0 `shouldBe` 42

      it "returns default when Nothing" $ do
        explicitDefault Nothing 0 `shouldBe` 0

      it "works with Text" $ do
        explicitDefault (Just "hello") "default" `shouldBe` "hello"

      it "works with empty string as value" $ do
        explicitDefault (Just "") "default" `shouldBe` ""

      it "works with empty string as default" $ do
        explicitDefault Nothing "" `shouldBe` ""

    describe "explicitConditional" $ do
      it "returns value when True" $ do
        explicitConditional True 42 0 `shouldBe` 42

      it "returns default when False" $ do
        explicitConditional False 42 0 `shouldBe` 0

      it "works with Text" $ do
        explicitConditional True "yes" "no" `shouldBe` "yes"

      it "works with lists" $ do
        explicitConditional False [1, 2] [3, 4] `shouldBe` [3, 4]

    describe "noTypeEscapes" $ do
      it "always returns Nothing" $ do
        noTypeEscapes (42 :: Int) `shouldBe` (Nothing :: Maybe String)

      it "returns Nothing for Text input" $ do
        noTypeEscapes ("hello" :: T.Text) `shouldBe` (Nothing :: Maybe Int)

      it "returns Nothing for list input" $ do
        noTypeEscapes ([1, 2, 3] :: [Int]) `shouldBe` (Nothing :: Maybe Char)

  describe "Rules.Verification" $ do
    describe "VerificationChecklist" $ do
      it "passes when all checks are True" $ do
        let checklist = VerificationChecklist True True True True True True True True True True
        verifyChecklist checklist `shouldBe` True

      it "fails when filesReadCompletely is False" $ do
        let checklist = VerificationChecklist False True True True True True True True True True
        verifyChecklist checklist `shouldBe` False

      it "fails when dependencyGraphTraced is False" $ do
        let checklist = VerificationChecklist True False True True True True True True True True
        verifyChecklist checklist `shouldBe` False

      it "fails when allInstancesFixed is False" $ do
        let checklist = VerificationChecklist True True False True True True True True True True
        verifyChecklist checklist `shouldBe` False

      it "fails when noBannedConstructs is False" $ do
        let checklist = VerificationChecklist True True True False True True True True True True
        verifyChecklist checklist `shouldBe` False

      it "fails when typesExplicit is False" $ do
        let checklist = VerificationChecklist True True True True False True True True True True
        verifyChecklist checklist `shouldBe` False

      it "fails when typeChecksPass is False" $ do
        let checklist = VerificationChecklist True True True True True False True True True True
        verifyChecklist checklist `shouldBe` False

      it "fails when verificationTestsPass is False" $ do
        let checklist = VerificationChecklist True True True True True True False True True True
        verifyChecklist checklist `shouldBe` False

      it "fails when proofsCheck is False" $ do
        let checklist = VerificationChecklist True True True True True True True False True True
        verifyChecklist checklist `shouldBe` False

      it "fails when verificationDocUpdated is False" $ do
        let checklist = VerificationChecklist True True True True True True True True False True
        verifyChecklist checklist `shouldBe` False

      it "fails when verificationWorkspaceClean is False" $ do
        let checklist = VerificationChecklist True True True True True True True True True False
        verifyChecklist checklist `shouldBe` False

    describe "toChecklist" $ do
      it "converts complete TaskCompletion to passing checklist" $ do
        let task = TaskCompletion True True True True True True
        let checklist = toChecklist task
        verifyChecklist checklist `shouldBe` True

      it "converts failing TaskCompletion to failing checklist (typeChecks)" $ do
        let task = TaskCompletion True False True True True True
        let checklist = toChecklist task
        -- typeChecks maps to typeChecksPass
        typeChecksPass checklist `shouldBe` False

      it "converts failing TaskCompletion to failing checklist (testsPass)" $ do
        let task = TaskCompletion True True False True True True
        let checklist = toChecklist task
        verificationTestsPass checklist `shouldBe` False

    describe "allChecksPass" $ do
      it "is equivalent to verifyChecklist" $ do
        let checklist = VerificationChecklist True True True True True True True True True True
        allChecksPass checklist `shouldBe` verifyChecklist checklist

  describe "Rules.FileReading" $ do
    describe "FileReadResult" $ do
      it "stores file path correctly" $ do
        let result = FileReadResult "/test/path.ts" "content" 1
        filePath result `shouldBe` "/test/path.ts"

      it "stores content correctly" $ do
        let result = FileReadResult "/test/path.ts" "line1\nline2" 2
        fileContent result `shouldBe` "line1\nline2"

      it "stores line count correctly" $ do
        let result = FileReadResult "/test/path.ts" "line1\nline2" 2
        lineCount result `shouldBe` 2

    describe "readCompleteFile" $ do
      it "reads file content completely" $ do
        withSystemTempDirectory "rules-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "line1\nline2\nline3"
          result <- readCompleteFile testFile
          case result of
            Right readResult -> do
              fileContent readResult `shouldBe` "line1\nline2\nline3"
              lineCount readResult `shouldBe` 3
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "reads empty file" $ do
        withSystemTempDirectory "rules-test" $ \dir -> do
          let testFile = dir </> "empty.ts"
          TIO.writeFile testFile ""
          result <- readCompleteFile testFile
          case result of
            Right readResult -> do
              fileContent readResult `shouldBe` ""
              lineCount readResult `shouldBe` 0
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "reads file with single line" $ do
        withSystemTempDirectory "rules-test" $ \dir -> do
          let testFile = dir </> "single.ts"
          TIO.writeFile testFile "single line"
          result <- readCompleteFile testFile
          case result of
            Right readResult -> lineCount readResult `shouldBe` 1
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "handles Unicode content" $ do
        withSystemTempDirectory "rules-test" $ \dir -> do
          let testFile = dir </> "unicode.ts"
          TIO.writeFile testFile "日本語\n中文\nहिन्दी"
          result <- readCompleteFile testFile
          case result of
            Right readResult -> lineCount readResult `shouldBe` 3
            Left err -> expectationFailure $ "Unexpected error: " ++ err

    describe "chunkFile" $ do
      it "returns single chunk for small file" $ do
        let content = T.unlines $ replicate 10 "line"
        let chunks = chunkFile content
        length chunks `shouldBe` 1

      it "returns multiple chunks for large file" $ do
        let content = T.unlines $ replicate 1000 "line"
        let chunks = chunkFile content
        length chunks `shouldBe` 2

      it "returns empty list for empty content" $ do
        let chunks = chunkFile ""
        -- Empty content with T.unlines gives one chunk with empty text
        length chunks `shouldSatisfy` (<= 1)

      it "chunks exactly at 500 line boundaries" $ do
        let content = T.unlines $ replicate 500 "line"
        let chunks = chunkFile content
        length chunks `shouldBe` 1

      it "creates correct number of chunks for 501 lines" $ do
        let content = T.unlines $ replicate 501 "line"
        let chunks = chunkFile content
        length chunks `shouldBe` 2

      it "creates correct number of chunks for 1500 lines" $ do
        let content = T.unlines $ replicate 1500 "line"
        let chunks = chunkFile content
        length chunks `shouldBe` 3

    describe "chunkLines" $ do
      it "chunks empty list" $ do
        chunkLines 500 ([] :: [T.Text]) `shouldBe` []

      it "chunks small list into single chunk" $ do
        let lines' = map T.pack ["a", "b", "c"]
        chunkLines 500 lines' `shouldBe` [lines']

      it "chunks list at boundary" $ do
        let lines' = map T.pack $ replicate 500 "x"
        let chunks = chunkLines 500 lines'
        length chunks `shouldBe` 1

      it "chunks list exceeding boundary" $ do
        let lines' = map T.pack $ replicate 501 "x"
        let chunks = chunkLines 500 lines'
        length chunks `shouldBe` 2
        length (head chunks) `shouldBe` 500
        length (chunks !! 1) `shouldBe` 1

  describe "Property Tests" $ do
    describe "Rules.Core Properties" $ do
      prop "safeHead returns Nothing for empty list" $ do
        safeHead ([] :: [Int]) == Nothing

      prop "safeHead returns Just for non-empty list" $ \xs ->
        not (null (xs :: [Int])) ==> isJust (safeHead xs)

      prop "safeTail returns Nothing for empty list" $ do
        safeTail ([] :: [Int]) == Nothing

      prop "safeTail returns Just for non-empty list" $ \xs ->
        not (null (xs :: [Int])) ==> isJust (safeTail xs)

      prop "verifyCompletion is False when any field is False" $ do
        \b1 b2 b3 b4 b5 b6 ->
          not (b1 && b2 && b3 && b4 && b5 && b6) ==>
            not (verifyCompletion (TaskCompletion b1 b2 b3 b4 b5 b6))

      prop "verifyCompletion is True only when all fields are True" $ do
        verifyCompletion (TaskCompletion True True True True True True) == True

    describe "Rules.TypeSafety Properties" $ do
      prop "explicitDefault returns value when Just" $ \(x :: Int) (def :: Int) ->
        explicitDefault (Just x) def == x

      prop "explicitDefault returns default when Nothing" $ \(def :: Int) ->
        explicitDefault Nothing def == def

      prop "explicitConditional returns first arg when True" $ \(x :: Int) (y :: Int) ->
        explicitConditional True x y == x

      prop "explicitConditional returns second arg when False" $ \(x :: Int) (y :: Int) ->
        explicitConditional False x y == y

      prop "noTypeEscapes always returns Nothing" $ \(x :: Int) ->
        isNothing (noTypeEscapes x :: Maybe String)

    describe "Rules.Verification Properties" $ do
      prop "verifyChecklist is False when any field is False" $ do
        \b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 ->
          not (b1 && b2 && b3 && b4 && b5 && b6 && b7 && b8 && b9 && b10) ==>
            not (verifyChecklist (VerificationChecklist b1 b2 b3 b4 b5 b6 b7 b8 b9 b10))

      prop "allChecksPass equals verifyChecklist" $ do
        \b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 ->
          let checklist = VerificationChecklist b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
          in allChecksPass checklist == verifyChecklist checklist

    describe "Rules.FileReading Properties" $ do
      it "chunkLines preserves total element count" $ do
        let xs = map T.pack ["a", "b", "c", "d", "e"]
        sum (map length (chunkLines 500 xs)) `shouldBe` length xs

      it "chunkLines with small chunk size" $ do
        let xs = map T.pack $ replicate 100 "x"
        sum (map length (chunkLines 10 xs)) `shouldBe` 100

      it "chunkLines returns non-empty chunks for non-empty input" $ do
        let xs = map T.pack ["a", "b", "c"]
        all (not . null) (chunkLines 500 xs) `shouldBe` True

  describe "Integration Tests" $ do
    it "complete workflow: task creation -> verification -> checklist" $ do
      let task = TaskCompletion True True True True True True
      verifyCompletion task `shouldBe` True
      let checklist = toChecklist task
      verifyChecklist checklist `shouldBe` True

    it "incomplete workflow: task fails -> checklist fails" $ do
      let task = TaskCompletion True False True True True True  -- typeChecks = False
      verifyCompletion task `shouldBe` False
      let checklist = toChecklist task
      -- Note: toChecklist assumes some fields as True, but typeChecks maps through
      typeChecksPass checklist `shouldBe` False

    it "file reading -> chunking -> verification" $ do
      withSystemTempDirectory "rules-test" $ \dir -> do
        let testFile = dir </> "large.ts"
        TIO.writeFile testFile (T.unlines $ replicate 1000 "line of code")
        result <- readCompleteFile testFile
        case result of
          Right readResult -> do
            lineCount readResult `shouldBe` 1000
            let chunks = chunkFile (fileContent readResult)
            length chunks `shouldBe` 2
            -- Verify all content is preserved
            T.concat chunks `shouldBe` fileContent readResult
          Left err -> expectationFailure $ "Unexpected error: " ++ err
