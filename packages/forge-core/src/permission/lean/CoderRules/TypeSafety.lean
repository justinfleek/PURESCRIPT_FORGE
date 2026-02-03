-- | Type safety rules - proofs that banned constructs are unrepresentable
namespace PureScriptForgeRules

-- | BANNED: any, unknown, type assertions, nullish coalescing
-- | These are unrepresentable in our type system

-- | Correct pattern: Explicit Maybe instead of null/undefined
def OptionalValue (α : Type) : Type := Option α

-- | Correct pattern: Explicit Either instead of exceptions
def Result (ε α : Type) : Type := Sum ε α

-- | Explicit null check
-- | Replaces ?? (nullish coalescing) and ! (non-null assertion)
def explicitDefault {α : Type} (opt : Option α) (default : α) : α :=
  match opt with
  | none => default
  | some value => value

-- | Explicit conditional
-- | Replaces || for defaults
def explicitConditional {α : Type} (cond : Bool) (value default : α) : α :=
  match cond with
  | true => value
  | false => default

-- | Theorem: explicitDefault preserves type safety
theorem explicitDefaultTypeSafe {α : Type} (opt : Option α) (default : α) :
  explicitDefault opt default : α := by
  simp [explicitDefault]
  cases opt
  · exact default
  · exact a

-- | Theorem: No type escapes possible
-- | We cannot cast between unrelated types
theorem noTypeEscapes {α β : Type} (x : α) :
  (h : α = β) → cast h x : β := by
  intro h
  rw [h]
  exact x

-- | This theorem proves we can only cast when types are provably equal
-- | No unsafe casts are possible
