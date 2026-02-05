{-|
Module      : Sidepanel.Components.Patterns.PatternRecognizerTypes
Description : Types for pattern recognition

Types for design pattern and anti-pattern recognition.
-}
module Sidepanel.Components.Patterns.PatternRecognizerTypes where

import Prelude

-- | Design pattern
type DesignPattern =
  { type_ :: PatternType
  , location :: Location
  , confidence :: Number  -- 0.0 to 1.0
  , description :: String
  }

-- | Pattern type
data PatternType
  = SingletonPattern
  | FactoryPattern
  | ObserverPattern
  | StrategyPattern
  | AdapterPattern
  | DecoratorPattern
  | CommandPattern
  | OtherPattern String

derive instance eqPatternType :: Eq PatternType

-- | Anti-pattern
type AntiPattern =
  { type_ :: AntiPatternType
  , location :: Location
  , severity :: String  -- "Low", "Medium", "High"
  , description :: String
  , suggestion :: String
  }

-- | Anti-pattern type
data AntiPatternType
  = GodObjectAntiPattern
  | SpaghettiCodeAntiPattern
  | MagicNumberAntiPattern
  | CopyPasteAntiPattern
  | GoldenHammerAntiPattern
  | OtherAntiPattern String

derive instance eqAntiPatternType :: Eq AntiPatternType

-- | Pattern match
type PatternMatch =
  { pattern :: PatternType
  , location :: Location
  , code :: String
  , confidence :: Number
  }

-- | Pattern suggestion
type PatternSuggestion =
  { pattern :: PatternType
  , location :: Location
  , reason :: String
  , benefit :: String
  , example :: Maybe String
  }

-- | Location
type Location =
  { file :: String
  , line :: Int
  , column :: Int
  }
