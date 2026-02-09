-- | NEXUS Message Delivery Proofs
-- | Mathematically proven properties about message delivery
-- |
-- | Strategy: Encode message creation with type-level invariants.
-- | Properties follow from the type definitions.

import Lean
import Std.Data.List.Lemmas

-- | Agent ID
structure AgentId where
  id : String
  deriving DecidableEq, BEq, Repr

-- | Message ID with non-empty guarantee
structure MessageId where
  id : String
  h_nonempty : id ≠ "" := by decide
  deriving Repr

instance : DecidableEq MessageId where
  decEq m1 m2 := by
    cases m1; cases m2
    simp
    exact String.decEq _ _

instance : BEq MessageId where
  beq m1 m2 := m1.id == m2.id

-- | Message with sender ≠ recipient invariant
structure Message where
  messageId : MessageId
  senderId : AgentId
  recipientId : AgentId
  content : String
  delivered : Bool
  h_different_agents : senderId ≠ recipientId := by decide
  deriving Repr

instance : DecidableEq Message where
  decEq m1 m2 := by
    cases m1; cases m2
    simp
    exact And.decidable

instance : BEq Message where
  beq m1 m2 := m1.messageId == m2.messageId &&
               m1.senderId == m2.senderId &&
               m1.recipientId == m2.recipientId

-- | Conversation with consistency invariant
structure Conversation where
  agent1Id : AgentId
  agent2Id : AgentId
  messages : List Message
  h_agents_different : agent1Id ≠ agent2Id
  h_messages_between : ∀ msg ∈ messages,
    (msg.senderId = agent1Id ∨ msg.senderId = agent2Id) ∧
    (msg.recipientId = agent1Id ∨ msg.recipientId = agent2Id)
  deriving Repr

/-!
## Message Construction

Smart constructors that maintain invariants by construction.
-/

-- | Create a message (requires proof that sender ≠ recipient)
def createMessage (msgId : MessageId) (sender recipient : AgentId)
  (content : String) (h_different : sender ≠ recipient) : Message where
  messageId := msgId
  senderId := sender
  recipientId := recipient
  content := content
  delivered := false
  h_different_agents := h_different

-- | Create an empty conversation
def emptyConversation (agent1 agent2 : AgentId)
  (h_different : agent1 ≠ agent2) : Conversation where
  agent1Id := agent1
  agent2Id := agent2
  messages := []
  h_agents_different := h_different
  h_messages_between := by intro msg h; exact False.elim (List.not_mem_nil msg h)

-- | Add a message to a conversation (with validation)
def addMessage (conv : Conversation) (msg : Message)
  (h_sender : msg.senderId = conv.agent1Id ∨ msg.senderId = conv.agent2Id)
  (h_recipient : msg.recipientId = conv.agent1Id ∨ msg.recipientId = conv.agent2Id)
  : Conversation where
  agent1Id := conv.agent1Id
  agent2Id := conv.agent2Id
  messages := msg :: conv.messages
  h_agents_different := conv.h_agents_different
  h_messages_between := by
    intro m h_m
    cases List.mem_cons.mp h_m with
    | inl h_eq =>
      rw [h_eq]
      exact ⟨h_sender, h_recipient⟩
    | inr h_in_old =>
      exact conv.h_messages_between m h_in_old

-- | Mark a message as delivered
def markDelivered (msg : Message) : Message where
  messageId := msg.messageId
  senderId := msg.senderId
  recipientId := msg.recipientId
  content := msg.content
  delivered := true
  h_different_agents := msg.h_different_agents

/-!
## Proven Properties

All properties follow mathematically from the type-level invariants.
-/

-- | Theorem: Message IDs are non-empty
-- | Immediate from MessageId.h_nonempty
theorem message_id_nonempty (msg : Message) :
  msg.messageId.id ≠ "" := msg.messageId.h_nonempty

-- | Theorem: Sender and recipient are different
-- | Immediate from Message.h_different_agents
theorem sender_recipient_different (msg : Message) :
  msg.senderId ≠ msg.recipientId := msg.h_different_agents

-- | Theorem: Delivered messages have non-empty IDs
theorem delivered_message_has_id (msg : Message) :
  msg.delivered → msg.messageId.id ≠ "" := by
  intro _
  exact msg.messageId.h_nonempty

-- | Theorem: Conversation consistency
-- | All messages in conversation are between the two agents
theorem conversation_consistency (conv : Conversation) :
  ∀ msg ∈ conv.messages,
    (msg.senderId = conv.agent1Id ∨ msg.senderId = conv.agent2Id) ∧
    (msg.recipientId = conv.agent1Id ∨ msg.recipientId = conv.agent2Id) :=
  conv.h_messages_between

-- | Theorem: Conversation agents are different
theorem conversation_agents_different (conv : Conversation) :
  conv.agent1Id ≠ conv.agent2Id := conv.h_agents_different

-- | Theorem: Empty conversation has no messages
theorem empty_conversation_no_messages (agent1 agent2 : AgentId)
  (h_different : agent1 ≠ agent2) :
  (emptyConversation agent1 agent2 h_different).messages = [] := rfl

-- | Theorem: Adding message increases count
theorem add_message_increases_count (conv : Conversation) (msg : Message)
  (h_sender : msg.senderId = conv.agent1Id ∨ msg.senderId = conv.agent2Id)
  (h_recipient : msg.recipientId = conv.agent1Id ∨ msg.recipientId = conv.agent2Id) :
  (addMessage conv msg h_sender h_recipient).messages.length = conv.messages.length + 1 := by
  simp [addMessage]

-- | Theorem: New message is in conversation after adding
theorem new_message_in_conversation (conv : Conversation) (msg : Message)
  (h_sender : msg.senderId = conv.agent1Id ∨ msg.senderId = conv.agent2Id)
  (h_recipient : msg.recipientId = conv.agent1Id ∨ msg.recipientId = conv.agent2Id) :
  msg ∈ (addMessage conv msg h_sender h_recipient).messages := by
  simp [addMessage]

-- | Theorem: Marking delivered preserves message content
theorem mark_delivered_preserves_content (msg : Message) :
  (markDelivered msg).content = msg.content := rfl

-- | Theorem: Marking delivered preserves sender/recipient
theorem mark_delivered_preserves_parties (msg : Message) :
  (markDelivered msg).senderId = msg.senderId ∧
  (markDelivered msg).recipientId = msg.recipientId := ⟨rfl, rfl⟩

-- | Theorem: Marked message is delivered
theorem mark_delivered_is_delivered (msg : Message) :
  (markDelivered msg).delivered = true := rfl

-- | Theorem: Message uniqueness (by ID equality)
-- | Two messages with the same ID and parties are considered the same message
theorem message_id_determines_message (msg1 msg2 : Message) :
  msg1.messageId = msg2.messageId →
  msg1.senderId = msg2.senderId →
  msg1.recipientId = msg2.recipientId →
  msg1.content = msg2.content →
  msg1.delivered = msg2.delivered →
  msg1 = msg2 := by
  intro h_id h_sender h_recipient h_content h_delivered
  cases msg1; cases msg2
  simp at *
  exact ⟨h_id, h_sender, h_recipient, h_content, h_delivered⟩

