-- | Lean4 proofs for OpenCode Message invariants
-- | Phase 2: Type Safety Layer
import Lean

namespace Opencode.Proofs.Message

-- | Message ID structure (non-empty string, like SessionID)
structure MessageID where
  value : String
  nonEmpty : value.length > 0

-- | Message structure with invariants
structure Message where
  id : MessageID  -- Changed from String to MessageID to enforce non-empty
  sessionID : String
  role : String  -- "user" | "assistant"
  parts : List String
  nonEmptyParts : parts.length > 0

-- | Message ID is never empty
theorem messageIdNonEmpty (msg : Message) : msg.id.value.length > 0 :=
  msg.id.nonEmpty

-- | Message has at least one part
theorem messageHasParts (msg : Message) : msg.parts.length > 0 :=
  msg.nonEmptyParts

-- | Token usage is non-negative
structure TokenUsage where
  prompt : Nat
  completion : Nat
  total : Nat
  nonNegative : prompt ≥ 0 ∧ completion ≥ 0 ∧ total ≥ 0
  totalCorrect : total = prompt + completion

theorem tokenUsageNonNegative (usage : TokenUsage) :
  usage.prompt ≥ 0 ∧ usage.completion ≥ 0 ∧ usage.total ≥ 0 :=
  usage.nonNegative

theorem tokenUsageTotalCorrect (usage : TokenUsage) :
  usage.total = usage.prompt + usage.completion :=
  usage.totalCorrect

end Opencode.Proofs.Message
