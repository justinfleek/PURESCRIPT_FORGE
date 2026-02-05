{-|
Module      : Sidepanel.Components.Patterns.PatternRecognizer
Description : Code pattern recognition - design patterns and anti-patterns

Recognizes design patterns and anti-patterns in code.
-}
module Sidepanel.Components.Patterns.PatternRecognizer where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Sidepanel.Components.Patterns.PatternRecognizerTypes
  ( DesignPattern
  , PatternType(..)
  , AntiPattern
  , AntiPatternType(..)
  , PatternMatch
  , PatternSuggestion
  )

-- | Recognize design patterns
recognizePatterns :: String -> String -> Aff (Array DesignPattern)
recognizePatterns filePath content = do
  let singletonPatterns = detectSingleton content
  let factoryPatterns = detectFactory content
  let observerPatterns = detectObserver content
  let strategyPatterns = detectStrategy content
  let adapterPatterns = detectAdapter content
  
  pure $ singletonPatterns <> factoryPatterns <> observerPatterns <>
         strategyPatterns <> adapterPatterns

-- | Detect Singleton pattern
detectSingleton :: String -> Array DesignPattern
detectSingleton content = do
  -- Pattern: Private constructor, static instance, getInstance method
  let hasPrivateConstructor = String.contains (String.Pattern "private") content &&
                              String.contains (String.Pattern "constructor") content
  let hasStaticInstance = String.contains (String.Pattern "static") content &&
                          String.contains (String.Pattern "instance") content
  let hasGetInstance = String.contains (String.Pattern "getInstance") content
  
  if hasPrivateConstructor && hasStaticInstance && hasGetInstance then
    [ { type_: SingletonPattern
      , location: { file: "", line: 0, column: 0 }
      , confidence: 0.8
      , description: "Singleton pattern detected: Single instance with private constructor"
      }
    ]
  else
    []

-- | Detect Factory pattern
detectFactory :: String -> Array DesignPattern
detectFactory content = do
  -- Pattern: Factory method that creates objects
  let hasFactoryMethod = String.contains (String.Pattern "create") content ||
                         String.contains (String.Pattern "factory") content ||
                         String.contains (String.Pattern "build") content
  let hasReturnType = String.contains (String.Pattern "return new") content ||
                      String.contains (String.Pattern "return {") content
  
  if hasFactoryMethod && hasReturnType then
    [ { type_: FactoryPattern
      , location: { file: "", line: 0, column: 0 }
      , confidence: 0.6
      , description: "Factory pattern detected: Method creates and returns objects"
      }
    ]
  else
    []

-- | Detect Observer pattern
detectObserver :: String -> Array DesignPattern
detectObserver content = do
  -- Pattern: Event listeners, subscribe/unsubscribe methods
  let hasSubscribe = String.contains (String.Pattern "subscribe") content ||
                     String.contains (String.Pattern "addListener") content ||
                     String.contains (String.Pattern "on(") content
  let hasNotify = String.contains (String.Pattern "notify") content ||
                  String.contains (String.Pattern "emit") content ||
                  String.contains (String.Pattern "trigger") content
  
  if hasSubscribe && hasNotify then
    [ { type_: ObserverPattern
      , location: { file: "", line: 0, column: 0 }
      , confidence: 0.7
      , description: "Observer pattern detected: Subscribe/notify mechanism"
      }
    ]
  else
    []

-- | Detect Strategy pattern
detectStrategy :: String -> Array DesignPattern
detectStrategy content = do
  -- Pattern: Interface/type with multiple implementations
  let hasInterface = String.contains (String.Pattern "interface") content ||
                     String.contains (String.Pattern "type class") content
  let hasImplementations = String.contains (String.Pattern "implements") content ||
                           String.contains (String.Pattern "instance") content
  
  if hasInterface && hasImplementations then
    [ { type_: StrategyPattern
      , location: { file: "", line: 0, column: 0 }
      , confidence: 0.6
      , description: "Strategy pattern detected: Interface with multiple implementations"
      }
    ]
  else
    []

-- | Detect Adapter pattern
detectAdapter :: String -> Array DesignPattern
detectAdapter content = do
  -- Pattern: Wrapper class that adapts interface
  let hasAdapter = String.contains (String.Pattern "adapter") content ||
                   String.contains (String.Pattern "wrapper") content
  let hasAdaptation = String.contains (String.Pattern "adapt") content ||
                      String.contains (String.Pattern "convert") content
  
  if hasAdapter && hasAdaptation then
    [ { type_: AdapterPattern
      , location: { file: "", line: 0, column: 0 }
      , confidence: 0.5
      , description: "Adapter pattern detected: Wrapper adapting interface"
      }
    ]
  else
    []

-- | Recognize anti-patterns
recognizeAntiPatterns :: String -> String -> Aff (Array AntiPattern)
recognizeAntiPatterns filePath content = do
  let godObjectPatterns = detectGodObject content
  let spaghettiCodePatterns = detectSpaghettiCode content
  let magicNumberPatterns = detectMagicNumbers content
  let copyPastePatterns = detectCopyPaste content
  let goldenHammerPatterns = detectGoldenHammer content
  
  pure $ godObjectPatterns <> spaghettiCodePatterns <> magicNumberPatterns <>
         copyPastePatterns <> goldenHammerPatterns

-- | Detect God Object anti-pattern
detectGodObject :: String -> Array AntiPattern
detectGodObject content = do
  -- Pattern: Class with too many responsibilities
  let classSize = String.length content
  let methodCount = countOccurrences content "function" + countOccurrences content "method"
  
  if classSize > 5000 && methodCount > 20 then
    [ { type_: GodObjectAntiPattern
      , location: { file: "", line: 0, column: 0 }
      , severity: "High"
      , description: "God Object anti-pattern: Class has too many responsibilities"
      , suggestion: "Break into smaller, focused classes"
      }
    ]
  else
    []

-- | Detect Spaghetti Code anti-pattern
detectSpaghettiCode :: String -> Array AntiPattern
detectSpaghettiCode content = do
  -- Pattern: High complexity, deep nesting, goto-like flow
  let complexity = calculateComplexity content
  let nestingDepth = calculateNestingDepth content
  
  if complexity > 20 && nestingDepth > 5 then
    [ { type_: SpaghettiCodeAntiPattern
      , location: { file: "", line: 0, column: 0 }
      , severity: "High"
      , description: "Spaghetti Code anti-pattern: High complexity and deep nesting"
      , suggestion: "Refactor to reduce complexity and nesting"
      }
    ]
  else
    []

-- | Detect Magic Numbers anti-pattern
detectMagicNumbers :: String -> Array AntiPattern
detectMagicNumbers content = do
  -- Pattern: Hardcoded numbers without explanation
  let magicNumbers = findMagicNumbers content
  
  if Array.length magicNumbers > 5 then
    [ { type_: MagicNumberAntiPattern
      , location: { file: "", line: 0, column: 0 }
      , severity: "Medium"
      , description: "Magic Numbers anti-pattern: Multiple hardcoded numbers without constants"
      , suggestion: "Replace magic numbers with named constants"
      }
    ]
  else
    []

-- | Find magic numbers
findMagicNumbers :: String -> Array Number
findMagicNumbers content = do
  -- Would use proper number extraction
  []

-- | Detect Copy-Paste anti-pattern
detectCopyPaste :: String -> Array AntiPattern
detectCopyPaste content = do
  -- Pattern: Code duplication
  let duplication = calculateDuplication content
  
  if duplication > 0.3 then
    [ { type_: CopyPasteAntiPattern
      , location: { file: "", line: 0, column: 0 }
      , severity: "Medium"
      , description: "Copy-Paste anti-pattern: High code duplication"
      , suggestion: "Extract duplicated code into reusable functions"
      }
    ]
  else
    []

-- | Calculate duplication
calculateDuplication :: String -> Number
calculateDuplication content = do
  -- Would use proper duplication detection
  0.0

-- | Detect Golden Hammer anti-pattern
detectGoldenHammer :: String -> Array AntiPattern
detectGoldenHammer content = do
  -- Pattern: Overuse of a single solution/pattern
  let patternFrequency = calculatePatternFrequency content
  
  if patternFrequency > 0.8 then
    [ { type_: GoldenHammerAntiPattern
      , location: { file: "", line: 0, column: 0 }
      , severity: "Low"
      , description: "Golden Hammer anti-pattern: Overuse of a single pattern"
      , suggestion: "Consider alternative approaches for different problems"
      }
    ]
  else
    []

-- | Calculate pattern frequency
calculatePatternFrequency :: String -> Number
calculatePatternFrequency content = do
  -- Would analyze pattern usage frequency
  0.0

-- | Suggest pattern application
suggestPattern :: String -> String -> Aff (Array PatternSuggestion)
suggestPattern filePath content = do
  -- Analyze code and suggest applicable patterns
  let suggestions = analyzeForPatternSuggestions content
  pure suggestions

-- | Analyze for pattern suggestions
analyzeForPatternSuggestions :: String -> Array PatternSuggestion
analyzeForPatternSuggestions content = do
  -- Would analyze code structure and suggest patterns
  []

-- | Calculate complexity
calculateComplexity :: String -> Number
calculateComplexity content =
  let ifCount = countOccurrences content "if"
      loopCount = countOccurrences content "for" + countOccurrences content "while"
  in
    Number.fromInt (1 + ifCount + loopCount)

-- | Calculate nesting depth
calculateNestingDepth :: String -> Int
calculateNestingDepth content =
  let lines = String.split (String.Pattern "\n") content
      maxDepth = Array.foldl (\maxDepth line ->
        let depth = calculateLineDepth line
        in
          if depth > maxDepth then depth else maxDepth
      ) 0 lines
  in
    maxDepth

-- | Calculate line depth
calculateLineDepth :: String -> Int
calculateLineDepth line =
  let indent = String.length (String.takeWhile (\c -> c == ' ' || c == '\t') line)
  in
    indent / 2

-- | Count occurrences
countOccurrences :: String -> String -> Int
countOccurrences str substr =
  let pattern = String.Pattern substr
  in
    String.split pattern str # Array.length # (_ - 1)
