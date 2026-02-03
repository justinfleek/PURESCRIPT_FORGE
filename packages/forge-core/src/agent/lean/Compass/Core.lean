/-
  Compass.Core - JSON infrastructure for COMPASS types

  Follows the TensorCore.Extract pattern exactly.
  Every type must have encode/decode + roundtrip proof.

  DO NOT add types without proofs.
-/

namespace Compass.Core

/-! ## JSON Model (mirrors TensorCore.Extract.Json) -/

inductive Json where
  | null : Json
  | bool : Bool → Json
  | num : Float → Json
  | int : Int → Json
  | str : String → Json
  | arr : List Json → Json
  | obj : List (String × Json) → Json
  deriving Repr, Inhabited

/-! ## JSON Accessors - designed for easy proof -/

/-- Get field from JSON object by direct pattern matching -/
def Json.getField (j : Json) (key : String) : Option Json :=
  match j with
  | .obj fields => fields.lookup key
  | _ => none

def Json.asString : Json → Option String
  | .str s => some s
  | _ => none

@[simp]
theorem Json.asString_str (s : String) : Json.asString (.str s) = some s := rfl

def Json.asInt : Json → Option Int
  | .int i => some i
  | _ => none

@[simp]
theorem Json.asInt_int (i : Int) : Json.asInt (.int i) = some i := rfl

def Json.asFloat : Json → Option Float
  | .num f => some f
  | _ => none

@[simp]
theorem Json.asFloat_num (f : Float) : Json.asFloat (.num f) = some f := rfl

def Json.asBool : Json → Option Bool
  | .bool b => some b
  | _ => none

@[simp]
theorem Json.asBool_bool (b : Bool) : Json.asBool (.bool b) = some b := rfl

def Json.asArray : Json → Option (List Json)
  | .arr xs => some xs
  | _ => none

def Json.asObject : Json → Option (List (String × Json))
  | .obj fields => some fields
  | _ => none

/-! ## Direct field access for proofs -/

/-- Access first field of a JSON object -/
def Json.field1 : Json → Option Json
  | .obj ((_, v) :: _) => some v
  | _ => none

/-- Access second field of a JSON object -/
def Json.field2 : Json → Option Json
  | .obj (_ :: (_, v) :: _) => some v
  | _ => none

/-- Access third field of a JSON object -/
def Json.field3 : Json → Option Json
  | .obj (_ :: _ :: (_, v) :: _) => some v
  | _ => none

/-- Access nth field of a JSON object -/
def Json.fieldN (n : Nat) (j : Json) : Option Json :=
  match j with
  | .obj fields => (fields[n]?).map Prod.snd
  | _ => none

@[simp]
theorem Json.fieldN_obj_zero (k : String) (v : Json) (rest : List (String × Json)) :
    Json.fieldN 0 (.obj ((k, v) :: rest)) = some v := rfl

@[simp]
theorem Json.fieldN_obj_succ (n : Nat) (kv : String × Json) (rest : List (String × Json)) :
    Json.fieldN (n + 1) (.obj (kv :: rest)) = Json.fieldN n (.obj rest) := rfl

/-! ## The Extractable Class - proof required -/

/--
  Types that can be extracted to external languages.

  You must provide:
  - encode/decode functions
  - A PROOF that they roundtrip

  No proof, no extraction.
-/
class Extractable (α : Type _) where
  encode : α → Json
  decode : Json → Option α
  proof : ∀ a, decode (encode a) = some a

/-! ## Base Instances with Proofs -/

instance : Extractable String where
  encode s := .str s
  decode j := j.asString
  proof _ := rfl

instance : Extractable Int where
  encode i := .int i
  decode j := j.asInt
  proof _ := rfl

instance : Extractable Float where
  encode f := .num f
  decode j := j.asFloat
  proof _ := rfl

instance : Extractable Bool where
  encode b := .bool b
  decode j := j.asBool
  proof _ := rfl

/-! ## DateTime representation -/

/-- ISO8601 timestamp as String (simplified for extraction) -/
abbrev DateTime := String

instance : Extractable DateTime where
  encode dt := .str dt
  decode j := j.asString
  proof _ := rfl

end Compass.Core
