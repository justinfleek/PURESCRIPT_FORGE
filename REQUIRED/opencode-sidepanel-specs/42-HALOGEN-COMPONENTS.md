# 42-HALOGEN-COMPONENTS: Component Patterns and Guidelines

## Overview

This document provides patterns for building Halogen components in the sidepanel, covering component structure, slots, queries, and composition.

---

## Component Anatomy

### Basic Component Structure

```purescript
module Sidepanel.Components.Example where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)

-- 1. Types
type Input = { initialValue :: Int }

type State = { value :: Int, isLoading :: Boolean }

data Action
  = Initialize
  | Increment
  | Decrement
  | Receive Input

data Output = ValueChanged Int

-- 2. Component definition
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

-- 3. Initial state from input
initialState :: Input -> State
initialState { initialValue } =
  { value: initialValue
  , isLoading: false
  }

-- 4. Render function
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "counter") ]
    [ HH.button
        [ HE.onClick \_ -> Decrement ]
        [ HH.text "-" ]
    , HH.span_ [ HH.text $ show state.value ]
    , HH.button
        [ HE.onClick \_ -> Increment ]
        [ HH.text "+" ]
    ]

-- 5. Action handler
handleAction :: forall m. MonadAff m 
             => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Increment -> do
    H.modify_ \s -> s { value = s.value + 1 }
    value <- H.gets _.value
    H.raise (ValueChanged value)
  
  Decrement -> do
    H.modify_ \s -> s { value = s.value - 1 }
    value <- H.gets _.value
    H.raise (ValueChanged value)
  
  Receive input ->
    H.modify_ _ { value = input.initialValue }
```

---

## Component with Child Slots

### Defining Slots

```purescript
module Sidepanel.Components.Parent where

import Type.Proxy (Proxy(..))

-- Child component types
type ChildSlots =
  ( counter :: H.Slot CounterQuery CounterOutput Int
  , modal :: H.Slot ModalQuery Void Unit
  )

-- Slot proxies
_counter = Proxy :: Proxy "counter"
_modal = Proxy :: Proxy "modal"

-- Using slots in render
render :: forall m. State -> H.ComponentHTML Action ChildSlots m
render state =
  HH.div_
    [ -- Single child
      HH.slot _modal unit Modal.component {} absurd
    
    -- Multiple children with index
    , HH.div_
        (mapWithIndex renderCounter state.counters)
    ]

renderCounter :: forall m. Int -> CounterData -> H.ComponentHTML Action ChildSlots m
renderCounter idx counterData =
  HH.slot _counter idx Counter.component 
    { initialValue: counterData.value }
    HandleCounterOutput
```

### Querying Children

```purescript
-- Query type for child
data CounterQuery a
  = GetValue (Int -> a)
  | SetValue Int a
  | Reset a

-- Parent querying child
handleAction = case _ of
  GetAllValues -> do
    values <- for (0 .. 9) \idx -> do
      H.request _counter idx (GetValue identity)
    -- values :: Array (Maybe Int)
    H.modify_ _ { allValues = catMaybes values }
  
  ResetAll -> do
    for_ (0 .. 9) \idx -> do
      H.tell _counter idx Reset
```

### Child Component with Query Support

```purescript
component :: forall i o m. MonadAff m => H.Component CounterQuery i o m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      }
  }

handleQuery :: forall a m. MonadAff m 
            => CounterQuery a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  GetValue reply -> do
    value <- H.gets _.value
    pure $ Just (reply value)
  
  SetValue newValue next -> do
    H.modify_ _ { value = newValue }
    pure $ Just next
  
  Reset next -> do
    H.modify_ _ { value = 0 }
    pure $ Just next
```

---

## Effects and Subscriptions

### Using Effects

```purescript
handleAction = case _ of
  FetchData -> do
    H.modify_ _ { isLoading = true }
    
    result <- H.liftAff $ fetchFromApi "/data"
    
    case result of
      Left error -> do
        H.modify_ _ { isLoading = false, error = Just error }
      Right data_ -> do
        H.modify_ _ { isLoading = false, data = Just data_ }
  
  SaveToStorage key value -> do
    H.liftEffect $ LocalStorage.setItem key value
```

### Event Subscriptions

```purescript
handleAction = case _ of
  Initialize -> do
    -- Subscribe to WebSocket messages
    void $ H.subscribe $ wsMessageEmitter
    
    -- Subscribe to timer
    void $ H.subscribe $ timerEmitter 1000
    
    -- Subscribe to window events
    void $ H.subscribe $ windowResizeEmitter

-- Emitter that fires WebSocket messages
wsMessageEmitter :: forall m. MonadAff m => H.Emitter m Action
wsMessageEmitter = H.Emitter \emit -> do
  ws <- liftEffect getWebSocket
  
  listener <- liftEffect $ eventListener \event -> do
    for_ (parseMessage event) \msg ->
      emit (HandleWsMessage msg)
  
  liftEffect $ addEventListener "message" listener ws
  
  -- Return cleanup function
  pure $ removeEventListener "message" listener ws

-- Timer emitter
timerEmitter :: forall m. MonadAff m => Int -> H.Emitter m Action
timerEmitter intervalMs = H.Emitter \emit -> do
  fiber <- Aff.forkAff $ forever do
    Aff.delay (Milliseconds $ toNumber intervalMs)
    liftEffect $ emit Tick
  
  pure $ Aff.killFiber (error "unsubscribed") fiber
```

---

## Common Patterns

### Loading State Pattern

```purescript
data RemoteData e a
  = NotAsked
  | Loading
  | Failure e
  | Success a

type State =
  { userData :: RemoteData String User
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  case state.userData of
    NotAsked ->
      HH.text "Click to load"
    Loading ->
      HH.div [ HP.class_ (H.ClassName "loading") ]
        [ HH.text "Loading..." ]
    Failure err ->
      HH.div [ HP.class_ (H.ClassName "error") ]
        [ HH.text $ "Error: " <> err ]
    Success user ->
      renderUser user
```

### Form Handling Pattern

```purescript
type FormState =
  { email :: String
  , password :: String
  , errors :: Map String String
  , isSubmitting :: Boolean
  }

data FormAction
  = UpdateEmail String
  | UpdatePassword String
  | Submit
  | SubmitResult (Either Error Response)

handleAction = case _ of
  UpdateEmail email -> do
    H.modify_ _ { email = email }
    validateField "email" email
  
  UpdatePassword password -> do
    H.modify_ _ { password = password }
    validateField "password" password
  
  Submit -> do
    state <- H.get
    when (Map.isEmpty state.errors) do
      H.modify_ _ { isSubmitting = true }
      result <- H.liftAff $ submitForm state
      handleAction (SubmitResult result)
  
  SubmitResult result -> do
    H.modify_ _ { isSubmitting = false }
    case result of
      Left err -> H.modify_ _ { errors = Map.singleton "form" (show err) }
      Right _ -> H.raise FormSubmitted

validateField :: String -> String -> H.HalogenM FormState FormAction () o m Unit
validateField field value = do
  let error = case field of
        "email" | not (isValidEmail value) -> Just "Invalid email"
        "password" | String.length value < 8 -> Just "Password too short"
        _ -> Nothing
  
  H.modify_ \s -> s { errors = case error of
    Just e -> Map.insert field e s.errors
    Nothing -> Map.delete field s.errors
  }
```

### Modal Pattern

```purescript
type ModalSlot = H.Slot ModalQuery Void Unit

data ModalQuery a
  = Open ModalContent a
  | Close a

data ModalOutput = ModalClosed

-- In parent
handleAction = case _ of
  ShowConfirmDialog -> do
    H.tell _modal unit (Open { title: "Confirm", body: "Are you sure?" })
  
  HandleModalOutput ModalClosed -> do
    -- Handle close
    pure unit

-- Modal component
modalComponent :: forall m. MonadAff m => H.Component ModalQuery Unit ModalOutput m
modalComponent = H.mkComponent
  { initialState: const { isOpen: false, content: Nothing }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleQuery = handleQuery }
  }

handleQuery = case _ of
  Open content next -> do
    H.modify_ _ { isOpen = true, content = Just content }
    pure $ Just next
  
  Close next -> do
    H.modify_ _ { isOpen = false }
    H.raise ModalClosed
    pure $ Just next
```

---

## Performance Tips

### Avoid Unnecessary Re-renders

```purescript
-- BAD: Creates new function every render
render state =
  HH.button
    [ HE.onClick \_ -> DoSomething state.value ]  -- Captures state
    [ HH.text "Click" ]

-- GOOD: Action doesn't capture state
render state =
  HH.button
    [ HE.onClick \_ -> DoSomethingWithCurrentState ]
    [ HH.text "Click" ]

handleAction = case _ of
  DoSomethingWithCurrentState -> do
    value <- H.gets _.value
    -- Use value here
```

### Memoization with `memo`

```purescript
-- Expensive computation
expensiveRender :: Data -> HTML
expensiveRender data_ = ...

-- Memoized version
render state =
  HH.lazy expensiveRender state.data
```

### Batching State Updates

```purescript
-- BAD: Multiple renders
handleAction = case _ of
  UpdateMultiple -> do
    H.modify_ _ { a = 1 }
    H.modify_ _ { b = 2 }
    H.modify_ _ { c = 3 }

-- GOOD: Single render
handleAction = case _ of
  UpdateMultiple -> do
    H.modify_ _ { a = 1, b = 2, c = 3 }
```

---

## Testing Components

```purescript
module Test.Components.CounterSpec where

import Test.Spec (Spec, describe, it)
import Halogen.Test.Driver as TD

spec :: Spec Unit
spec = describe "Counter" do
  it "increments value" do
    io <- TD.runUI Counter.component { initialValue: 0 }
    
    TD.send io Counter.Increment
    
    state <- TD.getState io
    state.value `shouldEqual` 1
  
  it "emits output on change" do
    io <- TD.runUI Counter.component { initialValue: 0 }
    
    TD.send io Counter.Increment
    
    outputs <- TD.getOutputs io
    outputs `shouldEqual` [Counter.ValueChanged 1]
```

---

## Related Specifications

- `40-PURESCRIPT-ARCHITECTURE.md` - Architecture overview
- `41-STATE-MANAGEMENT.md` - State patterns
- `85-CODE-STYLE-GUIDE.md` - Style conventions

---

*"Components are the atoms of UI. Make them small, composable, and testable."*
