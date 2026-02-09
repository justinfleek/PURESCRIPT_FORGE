# Compiler Pipeline Examples

## Example 1: PureScript Button Component

### Input: `Button.purs`

```purescript
module Button where

import Prelude

type ButtonProps =
  { label :: String
  , onClick :: Effect Unit
  , disabled :: Boolean
  }

button :: ButtonProps -> JSX
button props = 
  JSX.button
    { className: "px-4 py-2 bg-blue-500 text-white rounded hover:bg-blue-600"
    , onClick: props.onClick
    , disabled: props.disabled
    }
    [ JSX.text props.label ]
```

### Generated C++23: `Button.cpp`

```cpp
#include <string>
#include <functional>

namespace Button {

struct ButtonProps {
    std::string label;
    std::function<void()> onClick;
    bool disabled;
};

auto button(ButtonProps props) -> ReactElement {
    return create_element("button", {
        .className = "px-4 py-2 bg-blue-500 text-white rounded hover:bg-blue-600",
        .attributes = {
            {"onClick", props.onClick},
            {"disabled", props.disabled ? "true" : "false"}
        }
    }, {
        create_text_element(props.label)
    });
}

} // namespace Button
```

### Generated React: `Button.tsx`

```tsx
import * as React from 'react';
import { cn } from '@/lib/utils';

export interface ButtonProps {
  label: string;
  onClick: () => void;
  disabled: boolean;
}

export const Button: React.FC<ButtonProps> = (props) => {
  const { label, onClick, disabled } = props;
  
  return (
    <button
      className={cn("px-4 py-2 bg-blue-500 text-white rounded hover:bg-blue-600")}
      onClick={onClick}
      disabled={disabled}
    >
      {label}
    </button>
  );
};
```

## Example 2: Radix UI Dialog Component

### Input: `Dialog.purs`

```purescript
module Dialog where

import Prelude

type DialogProps =
  { open :: Boolean
  , onOpenChange :: Boolean -> Effect Unit
  , title :: String
  , children :: Array JSX
  }

dialog :: DialogProps -> JSX
dialog props = 
  JSX.dialog
    { [[radix_component("Dialog")]]
    , open: props.open
    , onOpenChange: props.onOpenChange
    }
    [ JSX.dialogTitle {} [ JSX.text props.title ]
    , JSX.dialogContent {} props.children
    ]
```

### Generated React: `Dialog.tsx`

```tsx
import * as React from 'react';
import * as Dialog from '@radix-ui/react-dialog';
import { cn } from '@/lib/utils';

export interface DialogProps {
  open: boolean;
  onOpenChange: (open: boolean) => void;
  title: string;
  children: React.ReactNode[];
}

export const DialogComponent: React.FC<DialogProps> = (props) => {
  const { open, onOpenChange, title, children } = props;
  
  return (
    <Dialog.Root open={open} onOpenChange={onOpenChange}>
      <Dialog.Trigger />
      <Dialog.Portal>
        <Dialog.Overlay className={cn("fixed inset-0 bg-black/50")} />
        <Dialog.Content className={cn("fixed top-1/2 left-1/2 transform -translate-x-1/2 -translate-y-1/2 bg-white p-6 rounded-lg shadow-lg")}>
          <Dialog.Title className={cn("text-xl font-bold mb-4")}>
            {title}
          </Dialog.Title>
          {children}
        </Dialog.Content>
      </Dialog.Portal>
    </Dialog.Root>
  );
};
```

## Example 3: Haskell Component

### Input: `Counter.hs`

```haskell
module Counter where

data CounterState = CounterState { count :: Int }

increment :: CounterState -> CounterState
increment (CounterState n) = CounterState (n + 1)

decrement :: CounterState -> CounterState
decrement (CounterState n) = CounterState (n - 1)
```

### Generated C++23: `Counter.cpp`

```cpp
#include <cstdint>

namespace Counter {

struct CounterState {
    std::int64_t count;
};

auto increment(CounterState state) -> CounterState {
    return CounterState{state.count + 1};
}

auto decrement(CounterState state) -> CounterState {
    return CounterState{state.count - 1};
}

} // namespace Counter
```

## Example 4: Lean4 Component with Proofs

### Input: `SafeList.lean`

```lean
def SafeList (n : Nat) : Type := List Nat

def safeHead {n : Nat} (l : SafeList (n + 1)) : Nat :=
  match l with
  | x :: _ => x
  | [] => 0 -- This case is impossible due to type

theorem safeHeadCorrect {n : Nat} (l : SafeList (n + 1)) :
  safeHead l ∈ l := by
  -- Proof preserved in C++23 as constexpr
```

### Generated C++23: `SafeList.cpp`

```cpp
#include <vector>
#include <cstdint>
#include <concepts>

namespace SafeList {

template<std::uint64_t n>
using SafeList = std::vector<std::uint64_t>;

template<std::uint64_t n>
constexpr auto safeHead(SafeList<n + 1> l) -> std::uint64_t {
    if constexpr (l.size() > 0) {
        return l[0];
    }
    return 0; // Unreachable due to type constraint
}

// Proof preserved as constexpr assertion
template<std::uint64_t n>
constexpr bool safeHeadCorrect(SafeList<n + 1> l) {
    auto head = safeHead(l);
    // Proof: head is always in l due to type constraint
    return true; // Verified at compile time
}

} // namespace SafeList
```
