-- Test Lean4 module for compiler pipeline

def CounterState : Type := { count : Nat }

def increment (state : CounterState) : CounterState :=
  { count := state.count + 1 }

def decrement (state : CounterState) : CounterState :=
  { count := state.count - 1 }

def maybeValue (opt : Option Nat) : Nat :=
  match opt with
  | some x => x
  | none => 0

theorem incrementCorrect (state : CounterState) :
  (increment state).count = state.count + 1 := by
  simp [increment]
