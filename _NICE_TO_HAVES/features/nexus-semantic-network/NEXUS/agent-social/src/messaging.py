"""
Nexus Agent Social - Messaging System
Agent-to-agent direct messaging
"""

from typing import List, Dict, Optional
from dataclasses import dataclass, field
from datetime import datetime
import uuid


@dataclass
class Message:
    """Direct message between agents"""
    message_id: str
    sender_id: str
    recipient_id: str
    content: str
    message_type: str  # text, link, discovery, post_share
    created_at: str = ""
    read_at: Optional[str] = None
    metadata: Dict = field(default_factory=dict)


@dataclass
class Conversation:
    """Conversation between two agents"""
    conversation_id: str
    agent1_id: str
    agent2_id: str
    messages: List[Message] = field(default_factory=list)
    last_message_at: str = ""
    unread_count_agent1: int = 0
    unread_count_agent2: int = 0


class MessagingSystem:
    """
    Messaging system for agent-to-agent direct messaging.
    
    Handles:
    - Sending messages
    - Receiving messages
    - Conversation management
    - Read receipts
    """
    
    def __init__(self):
        """Initialize messaging system"""
        self.conversations: Dict[str, Conversation] = {}
        self.agent_conversations: Dict[str, List[str]] = {}  # agent_id -> list of conversation_ids
        self.messages: Dict[str, Message] = {}
    
    def send_message(
        self,
        sender_id: str,
        recipient_id: str,
        content: str,
        message_type: str = "text"
    ) -> Message:
        """
        Send message from one agent to another.
        
        Args:
            sender_id: Sender agent ID
            recipient_id: Recipient agent ID
            content: Message content
            message_type: Message type
            
        Returns:
            Message
        """
        # Get or create conversation
        conversation = self._get_or_create_conversation(sender_id, recipient_id)
        
        # Create message
        message = Message(
            message_id=str(uuid.uuid4()),
            sender_id=sender_id,
            recipient_id=recipient_id,
            content=content,
            message_type=message_type,
            created_at=datetime.utcnow().isoformat()
        )
        
        self.messages[message.message_id] = message
        conversation.messages.append(message)
        conversation.last_message_at = message.created_at
        
        # Update unread count
        if conversation.agent1_id == recipient_id:
            conversation.unread_count_agent1 += 1
        else:
            conversation.unread_count_agent2 += 1
        
        return message
    
    def get_conversation(
        self,
        agent1_id: str,
        agent2_id: str
    ) -> Optional[Conversation]:
        """
        Get conversation between two agents.
        
        Args:
            agent1_id: First agent ID
            agent2_id: Second agent ID
            
        Returns:
            Conversation or None
        """
        conversation_id = self._get_conversation_id(agent1_id, agent2_id)
        return self.conversations.get(conversation_id)
    
    def get_conversations(self, agent_id: str) -> List[Conversation]:
        """
        Get all conversations for an agent.
        
        Args:
            agent_id: Agent ID
            
        Returns:
            List of conversations
        """
        conversation_ids = self.agent_conversations.get(agent_id, [])
        return [
            self.conversations[cid] for cid in conversation_ids
            if cid in self.conversations
        ]
    
    def mark_read(
        self,
        conversation_id: str,
        agent_id: str
    ) -> None:
        """
        Mark messages as read in conversation.
        
        Args:
            conversation_id: Conversation ID
            agent_id: Agent ID marking as read
        """
        if conversation_id not in self.conversations:
            return
        
        conversation = self.conversations[conversation_id]
        
        # Mark unread messages as read
        for message in conversation.messages:
            if message.recipient_id == agent_id and message.read_at is None:
                message.read_at = datetime.utcnow().isoformat()
        
        # Reset unread count
        if conversation.agent1_id == agent_id:
            conversation.unread_count_agent1 = 0
        else:
            conversation.unread_count_agent2 = 0
    
    def _get_or_create_conversation(
        self,
        agent1_id: str,
        agent2_id: str
    ) -> Conversation:
        """
        Get or create conversation between two agents.
        
        Args:
            agent1_id: First agent ID
            agent2_id: Second agent ID
            
        Returns:
            Conversation
        """
        conversation_id = self._get_conversation_id(agent1_id, agent2_id)
        
        if conversation_id in self.conversations:
            return self.conversations[conversation_id]
        
        # Create new conversation
        conversation = Conversation(
            conversation_id=conversation_id,
            agent1_id=agent1_id,
            agent2_id=agent2_id
        )
        
        self.conversations[conversation_id] = conversation
        
        # Update agent conversation lists
        if agent1_id not in self.agent_conversations:
            self.agent_conversations[agent1_id] = []
        self.agent_conversations[agent1_id].append(conversation_id)
        
        if agent2_id not in self.agent_conversations:
            self.agent_conversations[agent2_id] = []
        self.agent_conversations[agent2_id].append(conversation_id)
        
        return conversation
    
    def _get_conversation_id(self, agent1_id: str, agent2_id: str) -> str:
        """
        Get conversation ID for two agents (deterministic).
        
        Args:
            agent1_id: First agent ID
            agent2_id: Second agent ID
            
        Returns:
            Conversation ID
        """
        # Sort IDs to ensure consistent conversation ID
        sorted_ids = sorted([agent1_id, agent2_id])
        return f"conv_{sorted_ids[0]}_{sorted_ids[1]}"
