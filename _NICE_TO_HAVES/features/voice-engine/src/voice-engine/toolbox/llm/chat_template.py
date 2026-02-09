"""
Chat Template Parser - Qwen3/ChatML Format

Ground Truth: trtllm-serve-main/nix/openai-proxy-hs/ChatTemplate.hs
STRAYLIGHT_STANDARDS: Chat Template Standards

Parses and renders Qwen3/ChatML-style chat templates.

Format:
  <|im_start|>system
  You are a helpful assistant.<|im_end|>
  <|im_start|>user
  Hello<|im_end|>
  <|im_start|>assistant
  Hi there!<|im_end|>

Special tokens:
  <|im_start|>  - Start of message
  <|im_end|>    - End of message
  <|endoftext|> - End of sequence

Qwen3 thinking mode:
  <think>...</think>  - Model's internal reasoning (can be stripped)
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from enum import Enum
from typing import Literal, Optional

# Special tokens
IM_START = "<|im_start|>"
IM_END = "<|im_end|>"
END_OF_TEXT = "<|endoftext|>"
THINK_START = "<think>"
THINK_END = "</think>"


class Role(str, Enum):
    """Chat message role"""

    SYSTEM = "system"
    USER = "user"
    ASSISTANT = "assistant"
    TOOL = "tool"


@dataclass
class Message:
    """A single chat message"""

    role: Role
    content: str
    thought: Optional[str] = None  # Extracted <think> content

    def __post_init__(self) -> None:
        """Validate message"""
        if not isinstance(self.role, Role):
            raise TypeError(f"role must be Role, got {type(self.role)}")
        if not isinstance(self.content, str):
            raise TypeError(f"content must be str, got {type(self.content)}")
        if self.thought is not None and not isinstance(self.thought, str):
            raise TypeError(f"thought must be str or None, got {type(self.thought)}")


@dataclass
class Chat:
    """A complete chat conversation"""

    messages: list[Message]
    pending: Optional[Role] = None  # Role waiting for completion

    def __post_init__(self) -> None:
        """Validate chat"""
        if not isinstance(self.messages, list):
            raise TypeError(f"messages must be list, got {type(self.messages)}")
        if self.pending is not None and not isinstance(self.pending, Role):
            raise TypeError(f"pending must be Role or None, got {type(self.pending)}")


def parse_role(text: str) -> tuple[Role, int]:
    """
    Parse role name from text.

    Returns:
        (Role, end_index) - Role and position after role name

    Raises:
        ValueError: If role is invalid
    """
    text_lower = text.lower()
    for role in Role:
        if text_lower.startswith(role.value):
            return role, len(role.value)
    raise ValueError(f"Invalid role in: {text[:50]}")


def extract_thinking(content: str) -> tuple[str, Optional[str]]:
    """
    Extract thinking block from content.

    Returns:
        (cleaned_content, extracted_thought) - Content with think block removed, extracted thought

    STRAYLIGHT_STANDARDS: Thinking Block Extraction Algorithm
    """
    # Pattern: <think>...</think>
    pattern = rf"{re.escape(THINK_START)}(.*?){re.escape(THINK_END)}"
    match = re.search(pattern, content, re.DOTALL)

    if match:
        thought = match.group(1).strip()
        cleaned = re.sub(pattern, "", content, flags=re.DOTALL).strip()
        return cleaned, thought if thought else None

    return content, None


def strip_thinking(content: str) -> str:
    """
    Strip all thinking blocks from content.

    STRAYLIGHT_STANDARDS: Thinking Block Stripping Algorithm

    Handles:
    - Closed think blocks: <think>...</think>
    - Unclosed think blocks: <think>... (rest of text is thinking)
    """
    # Remove closed think blocks
    content = re.sub(
        rf"{re.escape(THINK_START)}.*?{re.escape(THINK_END)}",
        "",
        content,
        flags=re.DOTALL,
    )

    # Remove unclosed think blocks (everything after <think>)
    if THINK_START in content:
        idx = content.find(THINK_START)
        content = content[:idx].rstrip()

    return content.strip()


def parse_message(text: str, start_pos: int = 0) -> tuple[Message, int]:
    """
    Parse a single message from text.

    Args:
        text: Text to parse
        start_pos: Starting position in text

    Returns:
        (Message, end_pos) - Parsed message and position after message

    Raises:
        ValueError: If message format is invalid

    STRAYLIGHT_STANDARDS: Chat Template Parsing
    """
    pos = start_pos

    # Skip whitespace
    while pos < len(text) and text[pos] in " \n\t":
        pos += 1

    # Parse <|im_start|>
    if not text[pos:].startswith(IM_START):
        raise ValueError(f"Expected {IM_START} at position {pos}")

    pos += len(IM_START)

    # Parse role
    role, role_len = parse_role(text[pos:])
    pos += role_len

    # Skip optional newline
    if pos < len(text) and text[pos] == "\n":
        pos += 1

    # Parse content (until <|im_end|>)
    content_start = pos
    end_marker = text.find(IM_END, pos)
    if end_marker == -1:
        raise ValueError(f"Unclosed message: missing {IM_END}")

    content_raw = text[content_start:end_marker]
    pos = end_marker + len(IM_END)

    # Extract thinking blocks
    content, thought = extract_thinking(content_raw)

    return Message(role=role, content=content.strip(), thought=thought), pos


def parse_chat(text: str) -> Chat:
    """
    Parse complete chat conversation.

    Args:
        text: Chat template text

    Returns:
        Chat - Parsed chat with messages

    Raises:
        ValueError: If chat format is invalid

    STRAYLIGHT_STANDARDS: Chat Template Parsing
    """
    messages: list[Message] = []
    pos = 0
    pending: Optional[Role] = None

    # Skip leading whitespace
    while pos < len(text) and text[pos] in " \n\t":
        pos += 1

    # Parse all messages
    while pos < len(text):
        # Check for pending assistant prompt (no content yet)
        if text[pos:].startswith(IM_START):
            try:
                # Try to parse as complete message
                msg, new_pos = parse_message(text, pos)
                messages.append(msg)
                pos = new_pos
            except ValueError:
                # Might be pending prompt
                if text[pos:].startswith(IM_START):
                    role_start = pos + len(IM_START)
                    try:
                        role, _ = parse_role(text[role_start:])
                        pending = role
                        break
                    except ValueError:
                        raise ValueError(f"Invalid message format at position {pos}")
        else:
            # No more messages
            break

        # Skip whitespace between messages
        while pos < len(text) and text[pos] in " \n\t":
            pos += 1

    return Chat(messages=messages, pending=pending)


def render_role(role: Role) -> str:
    """Render role as text"""
    return role.value


def render_message(msg: Message, include_thought: bool = True) -> str:
    """
    Render single message with think blocks.

    Args:
        msg: Message to render
        include_thought: If True, include <think> blocks in output
    """
    content = msg.content

    # Add thinking block if present and requested
    if include_thought and msg.thought:
        content = f"{THINK_START}{msg.thought}{THINK_END}\n{content}"

    return f"{IM_START}{render_role(msg.role)}\n{content}{IM_END}"


def render_chat(chat: Chat, include_generation_prompt: bool = True) -> str:
    """
    Render chat for model input.

    Args:
        chat: Chat to render
        include_generation_prompt: If True, add assistant prompt at end for generation

    STRAYLIGHT_STANDARDS: Chat Template Rendering
    """
    parts: list[str] = []

    # Render all messages
    for msg in chat.messages:
        parts.append(render_message(msg))

    # Add generation prompt if requested
    if include_generation_prompt:
        if chat.pending:
            parts.append(f"{IM_START}{render_role(chat.pending)}\n")
        else:
            # Default to assistant if no pending role
            parts.append(f"{IM_START}{render_role(Role.ASSISTANT)}\n")

    return "\n".join(parts)


def render_chat_complete(chat: Chat) -> str:
    """Render chat without generation prompt"""
    return render_chat(chat, include_generation_prompt=False)


def from_openai(messages: list[dict[str, str]]) -> Chat:
    """
    Convert OpenAI format to Chat.

    OpenAI format:
        [
            {"role": "system", "content": "..."},
            {"role": "user", "content": "..."},
        ]

    Returns:
        Chat - Converted chat
    """
    chat_messages: list[Message] = []

    for msg_dict in messages:
        role_str = msg_dict.get("role", "")
        content = msg_dict.get("content", "")

        try:
            role = Role(role_str)
        except ValueError:
            raise ValueError(f"Invalid OpenAI role: {role_str}")

        chat_messages.append(Message(role=role, content=content))

    return Chat(messages=chat_messages)


def to_openai(chat: Chat) -> list[dict[str, str]]:
    """
    Convert Chat to OpenAI format.

    Returns:
        List of OpenAI message dicts
    """
    return [
        {"role": msg.role.value, "content": msg.content} for msg in chat.messages
    ]


def extract_assistant_response(text: str) -> str:
    """
    Extract assistant response from Triton output.

    Challenge: Triton echoes full prompt, so output includes:
        <|im_start|>system
        ...<|im_end|>
        <|im_start|>user
        ...<|im_end|>
        <|im_start|>assistant
        <think>...</think>
        Actual response here<|im_end|>

    Solution: Extract content after last "assistant\n" marker.

    STRAYLIGHT_STANDARDS: Response Extraction
    """
    # Try format with special tokens: <|im_start|>assistant\n...<|im_end|>
    pattern_with_tokens = rf"{re.escape(IM_START)}assistant\n(.*?){re.escape(IM_END)}"
    match = re.search(pattern_with_tokens, text, re.DOTALL)
    if match:
        response = match.group(1)
        # Strip thinking blocks
        return strip_thinking(response).strip()

    # Try format without special tokens: assistant\n...
    pattern_no_tokens = r"assistant\n(.*?)(?:\n<|im_start|>|$)"
    match = re.search(pattern_no_tokens, text, re.DOTALL)
    if match:
        response = match.group(1)
        return strip_thinking(response).strip()

    # Fallback: return as-is (might already be just the response)
    return strip_thinking(text).strip()


__all__ = [
    "Role",
    "Message",
    "Chat",
    "parse_chat",
    "render_message",
    "render_chat",
    "render_chat_complete",
    "extract_thinking",
    "strip_thinking",
    "from_openai",
    "to_openai",
    "extract_assistant_response",
    "IM_START",
    "IM_END",
    "THINK_START",
    "THINK_END",
]
