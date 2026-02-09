-- Test PureScript module for compiler pipeline
module Test where

import Prelude

-- | Simple button component
type ButtonProps =
  { label :: String
  , onClick :: Effect Unit
  , disabled :: Boolean
  }

button :: ButtonProps -> JSX
button props = 
  JSX.button
    { className: "px-4 py-2 bg-blue-500 text-white rounded"
    , onClick: props.onClick
    , disabled: props.disabled
    }
    [ JSX.text props.label ]

-- | Counter component with state
type CounterState = { count :: Int }

increment :: CounterState -> CounterState
increment state = state { count = state.count + 1 }

decrement :: CounterState -> CounterState
decrement state = state { count = state.count - 1 }

-- | Maybe example
maybeValue :: Maybe Int -> Int
maybeValue = case _ of
  Just x -> x
  Nothing -> 0

-- | Either example
eitherValue :: Either String Int -> Int
eitherValue = case _ of
  Right x -> x
  Left _ -> 0
