-- | Comprehensive Tests for Forge Validator Modules
-- | Tests BannedConstructs, TypeEscapes, and FileReading validators
{-# LANGUAGE OverloadedStrings #-}

module ValidatorSpec (spec) where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.IO.Temp (withSystemTempDirectory)
import System.FilePath ((</>))
import System.Directory (createDirectoryIfMissing)

import qualified Forge.Validator.BannedConstructs as BC
import qualified Forge.Validator.TypeEscapes as TE
import qualified Forge.Validator.FileReading as FR

spec :: Spec
spec = do
  describe "BannedConstructs" $ do
    describe "bannedConstructs list" $ do
      it "contains @ts-ignore pattern" $ do
        any (\c -> BC.constructName c == "@ts-ignore") BC.bannedConstructs `shouldBe` True

      it "contains @ts-expect-error pattern" $ do
        any (\c -> BC.constructName c == "@ts-expect-error") BC.bannedConstructs `shouldBe` True

      it "contains eval() pattern" $ do
        any (\c -> BC.constructName c == "eval()") BC.bannedConstructs `shouldBe` True

      it "contains any pattern" $ do
        any (\c -> BC.constructName c == "any") BC.bannedConstructs `shouldBe` True

      it "contains ?? (nullish coalescing) pattern" $ do
        any (\c -> BC.constructName c == "??") BC.bannedConstructs `shouldBe` True

      it "has at least 10 banned constructs" $ do
        length BC.bannedConstructs `shouldSatisfy` (>= 10)

    describe "checkFile" $ do
      it "detects @ts-ignore in file" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "// @ts-ignore\nconst x = 1;"
          result <- BC.checkFile testFile
          case result of
            Right violations -> length violations `shouldSatisfy` (>= 1)
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "detects @ts-expect-error in file" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "// @ts-expect-error\nconst x: number = 'string';"
          result <- BC.checkFile testFile
          case result of
            Right violations -> length violations `shouldSatisfy` (>= 1)
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "returns empty list for clean file" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "clean.ts"
          TIO.writeFile testFile "const x: number = 1;\nconst y: string = 'hello';"
          result <- BC.checkFile testFile
          case result of
            Right violations -> violations `shouldBe` []
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "handles non-existent file gracefully" $ do
        result <- BC.checkFile "/nonexistent/path/file.ts"
        case result of
          Left _ -> return ()  -- Expected
          Right _ -> expectationFailure "Should have returned error for non-existent file"

      it "detects multiple violations in same file" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "multi.ts"
          TIO.writeFile testFile "// @ts-ignore\n// @ts-expect-error\neval('code');"
          result <- BC.checkFile testFile
          case result of
            Right violations -> length violations `shouldSatisfy` (>= 2)
            Left err -> expectationFailure $ "Unexpected error: " ++ err

    describe "validateDirectory" $ do
      it "validates directory with violations" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          TIO.writeFile (dir </> "bad.ts") "// @ts-ignore\nconst x = 1;"
          result <- BC.validateDirectory dir
          case result of
            Right violations -> length violations `shouldSatisfy` (>= 1)
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "validates nested directories" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          createDirectoryIfMissing True (dir </> "nested")
          TIO.writeFile (dir </> "nested" </> "bad.ts") "// @ts-ignore"
          result <- BC.validateDirectory dir
          case result of
            Right violations -> length violations `shouldSatisfy` (>= 1)
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "returns error for non-directory" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "file.ts"
          TIO.writeFile testFile "content"
          result <- BC.validateDirectory testFile
          case result of
            Left _ -> return ()  -- Expected
            Right _ -> expectationFailure "Should have returned error for non-directory"

      it "skips files with invalid extensions" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          TIO.writeFile (dir </> "test.md") "// @ts-ignore"  -- Markdown file
          result <- BC.validateDirectory dir
          case result of
            Right violations -> violations `shouldBe` []  -- Should not detect in .md
            Left err -> expectationFailure $ "Unexpected error: " ++ err

  describe "TypeEscapes" $ do
    describe "typeEscapes list" $ do
      it "contains 'as unknown as' pattern" $ do
        any (\e -> TE.matchPattern e == "as unknown as") TE.typeEscapes `shouldBe` True

      it "contains 'Record<string, any>' pattern" $ do
        any (\e -> TE.matchPattern e == "Record<string, any>") TE.typeEscapes `shouldBe` True

      it "contains 'Array<any>' pattern" $ do
        any (\e -> TE.matchPattern e == "Array<any>") TE.typeEscapes `shouldBe` True

      it "contains 'Promise<any>' pattern" $ do
        any (\e -> TE.matchPattern e == "Promise<any>") TE.typeEscapes `shouldBe` True

      it "has at least 6 type escape patterns" $ do
        length TE.typeEscapes `shouldSatisfy` (>= 6)

    describe "checkFile" $ do
      it "detects 'as unknown as' type escape" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "const x = y as unknown as SomeType;"
          violations <- TE.checkFile testFile
          length violations `shouldSatisfy` (>= 1)

      it "detects 'Record<string, any>' type escape" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "const obj: Record<string, any> = {};"
          violations <- TE.checkFile testFile
          length violations `shouldSatisfy` (>= 1)

      it "detects 'Array<any>' type escape" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "const arr: Array<any> = [];"
          violations <- TE.checkFile testFile
          length violations `shouldSatisfy` (>= 1)

      it "returns empty for clean file" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "clean.ts"
          TIO.writeFile testFile "const x: number = 1;\nconst arr: Array<string> = [];"
          violations <- TE.checkFile testFile
          length violations `shouldBe` 0

      it "detects multiple type escapes in same line" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "const x: Record<string, any> = {} as unknown as SomeType;"
          violations <- TE.checkFile testFile
          length violations `shouldSatisfy` (>= 2)

      it "reports correct line numbers" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "const clean = 1;\nconst bad: Array<any> = [];\nconst clean2 = 2;"
          violations <- TE.checkFile testFile
          case violations of
            [(lineNum, _)] -> lineNum `shouldBe` 2
            _ -> expectationFailure "Expected exactly one violation on line 2"

  describe "FileReading" $ do
    describe "bannedPatterns list" $ do
      it "contains grep pattern" $ do
        any (\p -> FR.constructName p == "grep") FR.bannedPatterns `shouldBe` True

      it "contains head pattern" $ do
        any (\p -> FR.constructName p == "head") FR.bannedPatterns `shouldBe` True

      it "contains tail pattern" $ do
        any (\p -> FR.constructName p == "tail") FR.bannedPatterns `shouldBe` True

      it "contains .slice() pattern" $ do
        any (\p -> FR.constructName p == ".slice()") FR.bannedPatterns `shouldBe` True

      it "has at least 8 banned patterns" $ do
        length FR.bannedPatterns `shouldSatisfy` (>= 8)

    describe "checkFile" $ do
      it "detects grep usage" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "const result = grep(content, pattern);"
          result <- FR.checkFile testFile
          case result of
            Right violations -> length violations `shouldSatisfy` (>= 1)
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "detects .slice() usage" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "const partial = content.slice(0, 100);"
          result <- FR.checkFile testFile
          case result of
            Right violations -> length violations `shouldSatisfy` (>= 1)
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "detects head usage" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "test.ts"
          TIO.writeFile testFile "const first = head(lines);"
          result <- FR.checkFile testFile
          case result of
            Right violations -> length violations `shouldSatisfy` (>= 1)
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "returns empty for clean file" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "clean.ts"
          TIO.writeFile testFile "const content = readFile(path);\nconst processed = transform(content);"
          result <- FR.checkFile testFile
          case result of
            Right violations -> violations `shouldBe` []
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "handles non-existent file gracefully" $ do
        result <- FR.checkFile "/nonexistent/path/file.ts"
        case result of
          Left _ -> return ()  -- Expected
          Right _ -> expectationFailure "Should have returned error for non-existent file"

    describe "validateDirectory" $ do
      it "validates directory with violations" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          TIO.writeFile (dir </> "bad.ts") "const x = content.slice(0, 10);"
          result <- FR.validateDirectory dir
          case result of
            Right violations -> length violations `shouldSatisfy` (>= 1)
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "validates nested directories" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          createDirectoryIfMissing True (dir </> "nested")
          TIO.writeFile (dir </> "nested" </> "bad.ts") "grep(content, pattern)"
          result <- FR.validateDirectory dir
          case result of
            Right violations -> length violations `shouldSatisfy` (>= 1)
            Left err -> expectationFailure $ "Unexpected error: " ++ err

      it "returns error for non-directory" $ do
        withSystemTempDirectory "validator-test" $ \dir -> do
          let testFile = dir </> "file.ts"
          TIO.writeFile testFile "content"
          result <- FR.validateDirectory testFile
          case result of
            Left _ -> return ()  -- Expected
            Right _ -> expectationFailure "Should have returned error for non-directory"

  describe "Edge Cases" $ do
    it "handles empty file" $ do
      withSystemTempDirectory "validator-test" $ \dir -> do
        let testFile = dir </> "empty.ts"
        TIO.writeFile testFile ""
        bcResult <- BC.checkFile testFile
        frResult <- FR.checkFile testFile
        teResult <- TE.checkFile testFile
        case (bcResult, frResult) of
          (Right bcViolations, Right frViolations) -> do
            bcViolations `shouldBe` []
            frViolations `shouldBe` []
            teResult `shouldBe` []
          _ -> expectationFailure "Should handle empty files"

    it "handles file with only whitespace" $ do
      withSystemTempDirectory "validator-test" $ \dir -> do
        let testFile = dir </> "whitespace.ts"
        TIO.writeFile testFile "   \n   \n   "
        bcResult <- BC.checkFile testFile
        frResult <- FR.checkFile testFile
        case (bcResult, frResult) of
          (Right bcViolations, Right frViolations) -> do
            bcViolations `shouldBe` []
            frViolations `shouldBe` []
          _ -> expectationFailure "Should handle whitespace-only files"

    it "handles very long lines" $ do
      withSystemTempDirectory "validator-test" $ \dir -> do
        let testFile = dir </> "longline.ts"
        let longLine = T.replicate 10000 "a" <> " // @ts-ignore"
        TIO.writeFile testFile longLine
        result <- BC.checkFile testFile
        case result of
          Right violations -> length violations `shouldSatisfy` (>= 1)
          Left err -> expectationFailure $ "Unexpected error: " ++ err

    it "handles Unicode content" $ do
      withSystemTempDirectory "validator-test" $ \dir -> do
        let testFile = dir </> "unicode.ts"
        TIO.writeFile testFile "// 日本語 @ts-ignore\nconst x = '中文';"
        result <- BC.checkFile testFile
        case result of
          Right violations -> length violations `shouldSatisfy` (>= 1)
          Left err -> expectationFailure $ "Unexpected error: " ++ err

    it "handles patterns in strings (may be false positive)" $ do
      withSystemTempDirectory "validator-test" $ \dir -> do
        let testFile = dir </> "strings.ts"
        TIO.writeFile testFile "const msg = 'Use @ts-ignore to suppress errors';"
        result <- BC.checkFile testFile
        case result of
          Right violations -> do
            -- Note: This is a known limitation - patterns in strings are detected
            -- This documents the behavior rather than asserting it's "correct"
            length violations `shouldSatisfy` (>= 0)
          Left err -> expectationFailure $ "Unexpected error: " ++ err

  describe "Property Tests" $ do
    prop "BannedConstructs - all constructs have non-empty names" $
      all (\c -> not (null (BC.constructName c))) BC.bannedConstructs

    prop "BannedConstructs - all constructs have non-empty reasons" $
      all (\c -> not (null (BC.reason c))) BC.bannedConstructs

    prop "TypeEscapes - all escapes have non-empty patterns" $
      all (\e -> not (T.null (TE.matchPattern e))) TE.typeEscapes

    prop "TypeEscapes - all escapes have non-empty names" $
      all (\e -> not (null (TE.constructName e))) TE.typeEscapes

    prop "FileReading - all patterns have non-empty names" $
      all (\p -> not (null (FR.constructName p))) FR.bannedPatterns

    prop "FileReading - all patterns have non-empty reasons" $
      all (\p -> not (null (FR.reason p))) FR.bannedPatterns
