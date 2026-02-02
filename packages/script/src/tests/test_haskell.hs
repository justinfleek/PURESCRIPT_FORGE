-- Test Haskell module for compiler pipeline
module Test where

data CounterState = CounterState { count :: Int }

increment :: CounterState -> CounterState
increment (CounterState n) = CounterState (n + 1)

decrement :: CounterState -> CounterState
decrement (CounterState n) = CounterState (n - 1)

maybeValue :: Maybe Int -> Int
maybeValue (Just x) = x
maybeValue Nothing = 0

eitherValue :: Either String Int -> Int
eitherValue (Right x) = x
eitherValue (Left _) = 0
