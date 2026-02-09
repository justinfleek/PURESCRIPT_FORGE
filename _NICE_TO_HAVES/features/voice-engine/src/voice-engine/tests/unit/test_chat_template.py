"""
Deep comprehensive tests for chat template parsing and rendering.

Tests parsing, rendering, thinking extraction, OpenAI conversion, and bug detection.
"""
import pytest
from toolbox.llm.chat_template import (
    Role,
    Message,
    Chat,
    parse_chat,
    parse_message,
    parse_role,
    render_message,
    render_chat,
    render_chat_complete,
    extract_thinking,
    strip_thinking,
    from_openai,
    to_openai,
    extract_assistant_response,
    IM_START,
    IM_END,
    THINK_START,
    THINK_END,
)


class TestRole:
    """Deep comprehensive tests for Role enum."""

    def test_role_values(self):
        """Test all role values."""
        assert Role.SYSTEM.value == "system"
        assert Role.USER.value == "user"
        assert Role.ASSISTANT.value == "assistant"
        assert Role.TOOL.value == "tool"

    def test_role_from_string(self):
        """Test creating role from string."""
        assert Role("system") == Role.SYSTEM
        assert Role("user") == Role.USER
        assert Role("assistant") == Role.ASSISTANT
        assert Role("tool") == Role.TOOL

    def test_role_invalid_raises_error(self):
        """Test invalid role raises ValueError."""
        with pytest.raises(ValueError):
            Role("invalid")


class TestMessage:
    """Deep comprehensive tests for Message dataclass."""

    def test_message_creation(self):
        """Test message creation."""
        msg = Message(role=Role.USER, content="Hello")
        assert msg.role == Role.USER
        assert msg.content == "Hello"
        assert msg.thought is None

    def test_message_with_thought(self):
        """Test message with thought."""
        msg = Message(role=Role.ASSISTANT, content="Response", thought="thinking")
        assert msg.thought == "thinking"

    def test_message_invalid_role_raises_error(self):
        """Test invalid role type raises TypeError."""
        with pytest.raises(TypeError, match="role must be Role"):
            Message(role="user", content="test")  # type: ignore

    def test_message_invalid_content_raises_error(self):
        """Test invalid content type raises TypeError."""
        with pytest.raises(TypeError, match="content must be str"):
            Message(role=Role.USER, content=123)  # type: ignore

    def test_message_invalid_thought_raises_error(self):
        """Test invalid thought type raises TypeError."""
        with pytest.raises(TypeError, match="thought must be str or None"):
            Message(role=Role.USER, content="test", thought=123)  # type: ignore


class TestChat:
    """Deep comprehensive tests for Chat dataclass."""

    def test_chat_creation(self):
        """Test chat creation."""
        messages = [Message(role=Role.USER, content="Hello")]
        chat = Chat(messages=messages)
        assert len(chat.messages) == 1
        assert chat.pending is None

    def test_chat_with_pending(self):
        """Test chat with pending role."""
        messages = [Message(role=Role.USER, content="Hello")]
        chat = Chat(messages=messages, pending=Role.ASSISTANT)
        assert chat.pending == Role.ASSISTANT

    def test_chat_invalid_messages_raises_error(self):
        """Test invalid messages type raises TypeError."""
        with pytest.raises(TypeError, match="messages must be list"):
            Chat(messages="not a list")  # type: ignore

    def test_chat_invalid_pending_raises_error(self):
        """Test invalid pending type raises TypeError."""
        with pytest.raises(TypeError, match="pending must be Role or None"):
            Chat(messages=[], pending="not a role")  # type: ignore


class TestParseRole:
    """Deep comprehensive tests for parse_role function."""

    def test_parse_role_system(self):
        """Test parsing system role."""
        role, end_pos = parse_role("system")
        assert role == Role.SYSTEM
        assert end_pos == len("system")

    def test_parse_role_user(self):
        """Test parsing user role."""
        role, end_pos = parse_role("user")
        assert role == Role.USER
        assert end_pos == len("user")

    def test_parse_role_case_insensitive(self):
        """Test parsing role is case-insensitive."""
        role, _ = parse_role("SYSTEM")
        assert role == Role.SYSTEM

    def test_parse_role_with_suffix(self):
        """Test parsing role with suffix."""
        role, end_pos = parse_role("system\ncontent")
        assert role == Role.SYSTEM
        assert end_pos == len("system")

    def test_parse_role_invalid_raises_error(self):
        """Test invalid role raises ValueError."""
        with pytest.raises(ValueError, match="Invalid role"):
            parse_role("invalid")


class TestExtractThinking:
    """Deep comprehensive tests for extract_thinking function."""

    def test_extract_thinking_no_think_block(self):
        """Test extract_thinking with no think block."""
        content, thought = extract_thinking("Hello world")
        assert content == "Hello world"
        assert thought is None

    def test_extract_thinking_with_think_block(self):
        """Test extract_thinking with think block."""
        content, thought = extract_thinking("Hello <think>reasoning</think> world")
        assert thought == "reasoning"
        assert "Hello" in content
        assert "world" in content
        assert "<think>" not in content
        assert "</think>" not in content

    def test_extract_thinking_multiple_think_blocks(self):
        """Test extract_thinking with multiple think blocks."""
        # Should extract first block
        content, thought = extract_thinking(
            "<think>first</think> text <think>second</think>"
        )
        assert thought == "first"
        assert "text" in content

    def test_extract_thinking_empty_think_block(self):
        """Test extract_thinking with empty think block."""
        content, thought = extract_thinking("Hello <think></think> world")
        assert thought is None  # Empty thought returns None
        assert "Hello" in content
        assert "world" in content

    def test_extract_thinking_whitespace_only_think_block(self):
        """Test extract_thinking with whitespace-only think block."""
        content, thought = extract_thinking("Hello <think>   </think> world")
        assert thought is None  # Whitespace-only returns None after strip
        assert "Hello" in content

    def test_extract_thinking_multiline_think_block(self):
        """Test extract_thinking with multiline think block."""
        content, thought = extract_thinking(
            "Hello <think>line1\nline2\nline3</think> world"
        )
        assert thought == "line1\nline2\nline3"
        assert "Hello" in content
        assert "world" in content

    def test_extract_thinking_nested_tags(self):
        """Test extract_thinking with nested tags."""
        content, thought = extract_thinking(
            "Hello <think>inner <tag>content</tag></think> world"
        )
        assert "inner <tag>content</tag>" in thought
        assert "Hello" in content
        assert "world" in content


class TestStripThinking:
    """Deep comprehensive tests for strip_thinking function."""

    def test_strip_thinking_no_think_block(self):
        """Test strip_thinking with no think block."""
        result = strip_thinking("Hello world")
        assert result == "Hello world"

    def test_strip_thinking_with_think_block(self):
        """Test strip_thinking with closed think block."""
        result = strip_thinking("Hello <think>reasoning</think> world")
        assert result == "Hello world"
        assert "<think>" not in result
        assert "</think>" not in result

    def test_strip_thinking_multiple_think_blocks(self):
        """Test strip_thinking with multiple think blocks."""
        result = strip_thinking(
            "Hello <think>first</think> text <think>second</think> world"
        )
        assert result == "Hello text world"

    def test_strip_thinking_unclosed_think_block(self):
        """Test strip_thinking with unclosed think block."""
        result = strip_thinking("Hello <think>reasoning world")
        assert result == "Hello"
        assert "<think>" not in result

    def test_strip_thinking_unclosed_at_end(self):
        """Test strip_thinking with unclosed think block at end."""
        result = strip_thinking("Hello <think>reasoning")
        assert result == "Hello"

    def test_strip_thinking_multiline(self):
        """Test strip_thinking with multiline think block."""
        result = strip_thinking("Hello <think>line1\nline2</think> world")
        assert result == "Hello world"

    def test_strip_thinking_empty_content(self):
        """Test strip_thinking with empty content."""
        result = strip_thinking("")
        assert result == ""

    def test_strip_thinking_only_think_block(self):
        """Test strip_thinking with only think block."""
        result = strip_thinking("<think>reasoning</think>")
        assert result == ""

    def test_strip_thinking_whitespace_preservation(self):
        """Test strip_thinking preserves whitespace correctly."""
        result = strip_thinking("Hello   <think>reasoning</think>   world")
        assert "Hello" in result
        assert "world" in result


class TestParseMessage:
    """Deep comprehensive tests for parse_message function."""

    def test_parse_message_user(self):
        """Test parsing user message."""
        text = f"{IM_START}user\nHello{IM_END}"
        msg, end_pos = parse_message(text)
        assert msg.role == Role.USER
        assert msg.content == "Hello"
        assert end_pos == len(text)

    def test_parse_message_assistant(self):
        """Test parsing assistant message."""
        text = f"{IM_START}assistant\nHi there{IM_END}"
        msg, end_pos = parse_message(text)
        assert msg.role == Role.ASSISTANT
        assert msg.content == "Hi there"

    def test_parse_message_system(self):
        """Test parsing system message."""
        text = f"{IM_START}system\nYou are helpful{IM_END}"
        msg, end_pos = parse_message(text)
        assert msg.role == Role.SYSTEM
        assert msg.content == "You are helpful"

    def test_parse_message_with_think_block(self):
        """Test parsing message with think block."""
        text = f"{IM_START}assistant\nHello <think>reasoning</think> world{IM_END}"
        msg, end_pos = parse_message(text)
        assert msg.role == Role.ASSISTANT
        assert msg.content == "Hello world"
        assert msg.thought == "reasoning"

    def test_parse_message_no_newline_after_role(self):
        """Test parsing message without newline after role."""
        text = f"{IM_START}userHello{IM_END}"
        msg, end_pos = parse_message(text)
        assert msg.role == Role.USER
        assert msg.content == "Hello"

    def test_parse_message_multiple_spaces(self):
        """Test parsing message with multiple spaces."""
        text = f"{IM_START}user\n  Hello   world  {IM_END}"
        msg, end_pos = parse_message(text)
        assert msg.content == "Hello   world"  # Content preserves internal spaces

    def test_parse_message_unclosed_raises_error(self):
        """Test parsing unclosed message raises ValueError."""
        text = f"{IM_START}user\nHello"
        with pytest.raises(ValueError, match="Unclosed message"):
            parse_message(text)

    def test_parse_message_no_im_start_raises_error(self):
        """Test parsing message without IM_START raises ValueError."""
        text = "user\nHello"
        with pytest.raises(ValueError, match="Expected"):
            parse_message(text, start_pos=0)

    def test_parse_message_with_offset(self):
        """Test parsing message with start offset."""
        text = f"prefix {IM_START}user\nHello{IM_END}"
        msg, end_pos = parse_message(text, start_pos=7)
        assert msg.role == Role.USER
        assert msg.content == "Hello"


class TestParseChat:
    """Deep comprehensive tests for parse_chat function."""

    def test_parse_chat_single_message(self):
        """Test parsing single message."""
        text = f"{IM_START}user\nHello{IM_END}"
        chat = parse_chat(text)
        assert len(chat.messages) == 1
        assert chat.messages[0].role == Role.USER
        assert chat.messages[0].content == "Hello"

    def test_parse_chat_multiple_messages(self):
        """Test parsing multiple messages."""
        text = (
            f"{IM_START}system\nYou are helpful{IM_END}\n"
            f"{IM_START}user\nHello{IM_END}\n"
            f"{IM_START}assistant\nHi{IM_END}"
        )
        chat = parse_chat(text)
        assert len(chat.messages) == 3
        assert chat.messages[0].role == Role.SYSTEM
        assert chat.messages[1].role == Role.USER
        assert chat.messages[2].role == Role.ASSISTANT

    def test_parse_chat_with_pending(self):
        """Test parsing chat with pending assistant prompt."""
        text = (
            f"{IM_START}user\nHello{IM_END}\n"
            f"{IM_START}assistant\n"
        )
        chat = parse_chat(text)
        assert len(chat.messages) == 1
        assert chat.pending == Role.ASSISTANT

    def test_parse_chat_leading_whitespace(self):
        """Test parsing chat with leading whitespace."""
        text = f"\n  {IM_START}user\nHello{IM_END}"
        chat = parse_chat(text)
        assert len(chat.messages) == 1

    def test_parse_chat_empty_string(self):
        """Test parsing empty string."""
        chat = parse_chat("")
        assert len(chat.messages) == 0
        assert chat.pending is None

    def test_parse_chat_whitespace_only(self):
        """Test parsing whitespace-only string."""
        chat = parse_chat("   \n\t  ")
        assert len(chat.messages) == 0

    def test_parse_chat_invalid_message_raises_error(self):
        """Test parsing invalid message raises ValueError."""
        text = f"{IM_START}invalid_role\nHello{IM_END}"
        with pytest.raises(ValueError):
            parse_chat(text)


class TestRenderMessage:
    """Deep comprehensive tests for render_message function."""

    def test_render_message_user(self):
        """Test rendering user message."""
        msg = Message(role=Role.USER, content="Hello")
        result = render_message(msg)
        assert IM_START in result
        assert IM_END in result
        assert "user" in result
        assert "Hello" in result

    def test_render_message_with_thought(self):
        """Test rendering message with thought."""
        msg = Message(role=Role.ASSISTANT, content="Response", thought="reasoning")
        result = render_message(msg, include_thought=True)
        assert THINK_START in result
        assert THINK_END in result
        assert "reasoning" in result
        assert "Response" in result

    def test_render_message_without_thought(self):
        """Test rendering message without thought block."""
        msg = Message(role=Role.ASSISTANT, content="Response", thought="reasoning")
        result = render_message(msg, include_thought=False)
        assert THINK_START not in result
        assert THINK_END not in result
        assert "Response" in result


class TestRenderChat:
    """Deep comprehensive tests for render_chat function."""

    def test_render_chat_single_message(self):
        """Test rendering single message."""
        messages = [Message(role=Role.USER, content="Hello")]
        chat = Chat(messages=messages)
        result = render_chat(chat)
        assert IM_START in result
        assert "user" in result
        assert "Hello" in result
        assert "assistant" in result  # Generation prompt added

    def test_render_chat_multiple_messages(self):
        """Test rendering multiple messages."""
        messages = [
            Message(role=Role.SYSTEM, content="You are helpful"),
            Message(role=Role.USER, content="Hello"),
        ]
        chat = Chat(messages=messages)
        result = render_chat(chat)
        assert result.count(IM_START) == 3  # 2 messages + generation prompt

    def test_render_chat_with_pending(self):
        """Test rendering chat with pending role."""
        messages = [Message(role=Role.USER, content="Hello")]
        chat = Chat(messages=messages, pending=Role.ASSISTANT)
        result = render_chat(chat)
        assert "assistant" in result

    def test_render_chat_complete(self):
        """Test render_chat_complete without generation prompt."""
        messages = [Message(role=Role.USER, content="Hello")]
        chat = Chat(messages=messages)
        result = render_chat_complete(chat)
        assert result.count(IM_START) == 1  # No generation prompt
        assert "assistant" not in result

    def test_render_chat_empty(self):
        """Test rendering empty chat."""
        chat = Chat(messages=[])
        result = render_chat(chat)
        assert "assistant" in result  # Generation prompt still added


class TestFromOpenAI:
    """Deep comprehensive tests for from_openai function."""

    def test_from_openai_single_message(self):
        """Test converting single OpenAI message."""
        messages = [{"role": "user", "content": "Hello"}]
        chat = from_openai(messages)
        assert len(chat.messages) == 1
        assert chat.messages[0].role == Role.USER
        assert chat.messages[0].content == "Hello"

    def test_from_openai_multiple_messages(self):
        """Test converting multiple OpenAI messages."""
        messages = [
            {"role": "system", "content": "You are helpful"},
            {"role": "user", "content": "Hello"},
            {"role": "assistant", "content": "Hi"},
        ]
        chat = from_openai(messages)
        assert len(chat.messages) == 3

    def test_from_openai_empty_content(self):
        """Test converting message with empty content."""
        messages = [{"role": "user", "content": ""}]
        chat = from_openai(messages)
        assert chat.messages[0].content == ""

    def test_from_openai_invalid_role_raises_error(self):
        """Test invalid role raises ValueError."""
        messages = [{"role": "invalid", "content": "Hello"}]
        with pytest.raises(ValueError, match="Invalid OpenAI role"):
            from_openai(messages)

    def test_from_openai_missing_role(self):
        """Test missing role uses empty string."""
        messages = [{"role": "", "content": "Hello"}]
        with pytest.raises(ValueError):
            from_openai(messages)

    def test_from_openai_missing_content(self):
        """Test missing content uses empty string."""
        messages = [{"role": "user", "content": ""}]
        chat = from_openai(messages)
        assert chat.messages[0].content == ""


class TestToOpenAI:
    """Deep comprehensive tests for to_openai function."""

    def test_to_openai_single_message(self):
        """Test converting single message to OpenAI format."""
        messages = [Message(role=Role.USER, content="Hello")]
        chat = Chat(messages=messages)
        result = to_openai(chat)
        assert len(result) == 1
        assert result[0]["role"] == "user"
        assert result[0]["content"] == "Hello"

    def test_to_openai_multiple_messages(self):
        """Test converting multiple messages."""
        messages = [
            Message(role=Role.SYSTEM, content="You are helpful"),
            Message(role=Role.USER, content="Hello"),
        ]
        chat = Chat(messages=messages)
        result = to_openai(chat)
        assert len(result) == 2
        assert result[0]["role"] == "system"
        assert result[1]["role"] == "user"

    def test_to_openai_preserves_content(self):
        """Test to_openai preserves content."""
        messages = [Message(role=Role.USER, content="Hello world")]
        chat = Chat(messages=messages)
        result = to_openai(chat)
        assert result[0]["content"] == "Hello world"

    def test_to_openai_empty_chat(self):
        """Test converting empty chat."""
        chat = Chat(messages=[])
        result = to_openai(chat)
        assert len(result) == 0


class TestExtractAssistantResponse:
    """Deep comprehensive tests for extract_assistant_response function."""

    def test_extract_assistant_response_with_tokens(self):
        """Test extracting response with special tokens."""
        text = (
            f"{IM_START}system\nYou are helpful{IM_END}\n"
            f"{IM_START}user\nHello{IM_END}\n"
            f"{IM_START}assistant\nResponse here{IM_END}"
        )
        result = extract_assistant_response(text)
        assert result == "Response here"

    def test_extract_assistant_response_with_think_block(self):
        """Test extracting response with think block."""
        text = (
            f"{IM_START}assistant\n"
            f"<think>reasoning</think>\n"
            f"Response here{IM_END}"
        )
        result = extract_assistant_response(text)
        assert result == "Response here"
        assert "<think>" not in result

    def test_extract_assistant_response_without_tokens(self):
        """Test extracting response without special tokens."""
        text = "assistant\nResponse here"
        result = extract_assistant_response(text)
        assert result == "Response here"

    def test_extract_assistant_response_already_extracted(self):
        """Test extracting response that's already just the response."""
        text = "Response here"
        result = extract_assistant_response(text)
        assert result == "Response here"

    def test_extract_assistant_response_multiple_assistant_blocks(self):
        """Test extracting response from multiple assistant blocks."""
        text = (
            f"{IM_START}assistant\nFirst{IM_END}\n"
            f"{IM_START}assistant\nSecond{IM_END}"
        )
        result = extract_assistant_response(text)
        # Should extract last assistant block
        assert "Second" in result

    def test_extract_assistant_response_empty(self):
        """Test extracting empty response."""
        text = f"{IM_START}assistant\n{IM_END}"
        result = extract_assistant_response(text)
        assert result == ""


class TestBugDetection:
    """Bug detection tests for chat template."""

    def test_bug_parse_message_may_not_handle_nested_tags(self):
        """BUG: parse_message may not handle nested tags correctly."""
        # Nested tags in content may cause parsing issues
        # This test documents the potential issue
        # TODO: Add test with nested tags

    def test_bug_extract_thinking_may_not_handle_overlapping_tags(self):
        """BUG: extract_thinking may not handle overlapping tags."""
        # Overlapping <think> tags may cause incorrect extraction
        # This test documents the potential issue
        # TODO: Add test with overlapping tags

    def test_bug_strip_thinking_may_not_handle_partial_tags(self):
        """BUG: strip_thinking may not handle partial tags correctly."""
        # Partial tags like "<think" or "think>" may not be handled
        # This test documents the potential issue
        # TODO: Add test with partial tags

    def test_bug_parse_chat_may_not_handle_malformed_messages(self):
        """BUG: parse_chat may not handle malformed messages correctly."""
        # Malformed messages may cause parsing to fail or skip incorrectly
        # This test documents the potential issue
        # TODO: Add test with malformed messages

    def test_bug_render_chat_may_not_preserve_whitespace(self):
        """BUG: render_chat may not preserve whitespace correctly."""
        # Whitespace in content may be modified during rendering
        # This test documents the potential issue
        # TODO: Add test to verify whitespace preservation

    def test_bug_extract_assistant_response_may_not_handle_multiple_think_blocks(self):
        """BUG: extract_assistant_response may not handle multiple think blocks."""
        # Multiple think blocks may cause incorrect extraction
        # This test documents the potential issue
        # TODO: Add test with multiple think blocks
