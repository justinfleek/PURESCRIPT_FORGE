"""
Deep comprehensive tests for ThinkFilter streaming filter.

Tests incremental token filtering, state transitions, partial tags, and bug detection.
"""
import pytest
from toolbox.llm.think_filter import (
    ThinkState,
    ThinkFilter,
    ThinkResult,
    init_think_filter,
    feed_think_filter,
    finalize_think_filter,
    THINK_START,
    THINK_END,
)


class TestInitThinkFilter:
    """Deep comprehensive tests for init_think_filter function."""

    def test_init_think_filter(self):
        """Test initializing think filter."""
        filter = init_think_filter()
        assert filter.state == ThinkState.OUTSIDE_THINK
        assert filter.buffer == ""

    def test_init_think_filter_type(self):
        """Test init_think_filter returns ThinkFilter."""
        filter = init_think_filter()
        assert isinstance(filter, ThinkFilter)


class TestFeedThinkFilter:
    """Deep comprehensive tests for feed_think_filter function."""

    def test_feed_normal_text(self):
        """Test feeding normal text (no think blocks)."""
        filter = init_think_filter()
        result = feed_think_filter(filter, "Hello world")
        assert result.output == "Hello world"
        assert result.filter.state == ThinkState.OUTSIDE_THINK
        assert result.filter.buffer == ""

    def test_feed_text_with_think_block(self):
        """Test feeding text with complete think block."""
        filter = init_think_filter()
        text = f"Hello {THINK_START}reasoning{THINK_END} world"
        result = feed_think_filter(filter, text)
        assert result.output == "Hello  world"
        assert "<think>" not in result.output
        assert "reasoning" not in result.output
        assert result.filter.state == ThinkState.OUTSIDE_THINK

    def test_feed_partial_think_start(self):
        """Test feeding partial think start tag."""
        filter = init_think_filter()
        result1 = feed_think_filter(filter, "Hello <thi")
        assert result1.output == "Hello "
        assert result1.filter.state == ThinkState.OUTSIDE_THINK
        assert result1.filter.buffer == "<thi"
        
        result2 = feed_think_filter(result1.filter, "nk>reasoning</think>")
        assert result2.output == ""
        assert result2.filter.state == ThinkState.OUTSIDE_THINK
        assert "reasoning" not in result2.output

    def test_feed_partial_think_end(self):
        """Test feeding partial think end tag."""
        filter = init_think_filter()
        result1 = feed_think_filter(filter, f"{THINK_START}reasoning</thi")
        assert result1.output == ""
        assert result1.filter.state == ThinkState.INSIDE_THINK
        assert result1.filter.buffer == "</thi"
        
        result2 = feed_think_filter(result1.filter, "nk>")
        assert result2.output == ""
        assert result2.filter.state == ThinkState.OUTSIDE_THINK

    def test_feed_multiple_think_blocks(self):
        """Test feeding multiple think blocks."""
        filter = init_think_filter()
        text = f"Hello {THINK_START}first{THINK_END} text {THINK_START}second{THINK_END} world"
        result = feed_think_filter(filter, text)
        assert result.output == "Hello  text  world"
        assert "first" not in result.output
        assert "second" not in result.output

    def test_feed_unclosed_think_block(self):
        """Test feeding unclosed think block."""
        filter = init_think_filter()
        text = f"Hello {THINK_START}reasoning"
        result = feed_think_filter(filter, text)
        assert result.output == "Hello "
        assert result.filter.state == ThinkState.INSIDE_THINK
        assert "reasoning" not in result.output

    def test_feed_empty_token(self):
        """Test feeding empty token."""
        filter = init_think_filter()
        result = feed_think_filter(filter, "")
        assert result.output == ""
        assert result.filter.state == ThinkState.OUTSIDE_THINK

    def test_feed_only_think_block(self):
        """Test feeding only think block."""
        filter = init_think_filter()
        text = f"{THINK_START}reasoning{THINK_END}"
        result = feed_think_filter(filter, text)
        assert result.output == ""
        assert "reasoning" not in result.output

    def test_feed_think_block_at_start(self):
        """Test feeding think block at start."""
        filter = init_think_filter()
        text = f"{THINK_START}reasoning{THINK_END}Hello"
        result = feed_think_filter(filter, text)
        assert result.output == "Hello"
        assert "reasoning" not in result.output

    def test_feed_think_block_at_end(self):
        """Test feeding think block at end."""
        filter = init_think_filter()
        text = f"Hello{THINK_START}reasoning{THINK_END}"
        result = feed_think_filter(filter, text)
        assert result.output == "Hello"
        assert "reasoning" not in result.output

    def test_feed_multiple_tokens(self):
        """Test feeding multiple tokens incrementally."""
        filter = init_think_filter()
        
        result1 = feed_think_filter(filter, "Hello ")
        assert result1.output == "Hello "
        
        result2 = feed_think_filter(result1.filter, f"{THINK_START}reasoning{THINK_END}")
        assert result2.output == ""
        
        result3 = feed_think_filter(result2.filter, " world")
        assert result3.output == " world"
        
        # Combined output
        assert "Hello" in result1.output
        assert "world" in result3.output
        assert "reasoning" not in result1.output
        assert "reasoning" not in result2.output
        assert "reasoning" not in result3.output

    def test_feed_nested_think_blocks(self):
        """Test feeding nested think blocks (edge case)."""
        filter = init_think_filter()
        # Nested think blocks are not valid, but should be handled
        text = f"{THINK_START}outer {THINK_START}inner{THINK_END} outer{THINK_END}"
        result = feed_think_filter(filter, text)
        # Should filter entire block
        assert result.output == ""
        assert result.filter.state == ThinkState.OUTSIDE_THINK

    def test_feed_think_block_with_newlines(self):
        """Test feeding think block with newlines."""
        filter = init_think_filter()
        text = f"Hello {THINK_START}line1\nline2\nline3{THINK_END} world"
        result = feed_think_filter(filter, text)
        assert result.output == "Hello  world"
        assert "line1" not in result.output
        assert "line2" not in result.output
        assert "line3" not in result.output

    def test_feed_state_transition_outside_to_inside(self):
        """Test state transition from OUTSIDE_THINK to INSIDE_THINK."""
        filter = init_think_filter()
        assert filter.state == ThinkState.OUTSIDE_THINK
        
        result = feed_think_filter(filter, f"Hello {THINK_START}")
        assert result.filter.state == ThinkState.INSIDE_THINK
        assert result.output == "Hello "

    def test_feed_state_transition_inside_to_outside(self):
        """Test state transition from INSIDE_THINK to OUTSIDE_THINK."""
        filter = ThinkFilter(state=ThinkState.INSIDE_THINK, buffer="")
        result = feed_think_filter(filter, f"reasoning{THINK_END}")
        assert result.filter.state == ThinkState.OUTSIDE_THINK
        assert result.output == ""

    def test_feed_buffer_preservation(self):
        """Test buffer is preserved across partial tags."""
        filter = init_think_filter()
        result1 = feed_think_filter(filter, "Hello <thi")
        assert result1.filter.buffer == "<thi"
        
        result2 = feed_think_filter(result1.filter, "nk>")
        # Buffer should be cleared after complete tag
        assert result2.filter.buffer == ""


class TestFinalizeThinkFilter:
    """Deep comprehensive tests for finalize_think_filter function."""

    def test_finalize_outside_think(self):
        """Test finalizing filter in OUTSIDE_THINK state."""
        filter = ThinkFilter(state=ThinkState.OUTSIDE_THINK, buffer="remaining text")
        result = finalize_think_filter(filter)
        assert result == "remaining text"

    def test_finalize_inside_think(self):
        """Test finalizing filter in INSIDE_THINK state."""
        filter = ThinkFilter(state=ThinkState.INSIDE_THINK, buffer="thinking content")
        result = finalize_think_filter(filter)
        assert result == ""  # Discarded

    def test_finalize_empty_buffer_outside(self):
        """Test finalizing with empty buffer in OUTSIDE_THINK."""
        filter = ThinkFilter(state=ThinkState.OUTSIDE_THINK, buffer="")
        result = finalize_think_filter(filter)
        assert result == ""

    def test_finalize_empty_buffer_inside(self):
        """Test finalizing with empty buffer in INSIDE_THINK."""
        filter = ThinkFilter(state=ThinkState.INSIDE_THINK, buffer="")
        result = finalize_think_filter(filter)
        assert result == ""


class TestThinkFilterIntegration:
    """Integration tests for think filter."""

    def test_complete_stream_filtering(self):
        """Test complete stream filtering scenario."""
        filter = init_think_filter()
        tokens = [
            "Hello ",
            f"{THINK_START}",
            "reasoning ",
            "content",
            f"{THINK_END}",
            " world",
        ]
        
        outputs = []
        current_filter = filter
        for token in tokens:
            result = feed_think_filter(current_filter, token)
            outputs.append(result.output)
            current_filter = result.filter
        
        # Finalize
        final_output = finalize_think_filter(current_filter)
        outputs.append(final_output)
        
        combined = "".join(outputs)
        assert "Hello" in combined
        assert "world" in combined
        assert "reasoning" not in combined
        assert "content" not in combined

    def test_partial_tag_across_tokens(self):
        """Test partial tag split across multiple tokens."""
        filter = init_think_filter()
        
        # Tag split: "<think" | ">reasoning</think>"
        result1 = feed_think_filter(filter, "Hello <think")
        assert result1.output == "Hello "
        assert result1.filter.state == ThinkState.OUTSIDE_THINK
        
        result2 = feed_think_filter(result1.filter, ">reasoning</think>")
        assert result2.output == ""
        assert result2.filter.state == ThinkState.OUTSIDE_THINK
        
        result3 = feed_think_filter(result2.filter, " world")
        assert result3.output == " world"

    def test_multiple_partial_tags(self):
        """Test multiple partial tags across tokens."""
        filter = init_think_filter()
        
        result1 = feed_think_filter(filter, "<thi")
        assert result1.filter.buffer == "<thi"
        
        result2 = feed_think_filter(result1.filter, "nk>content</thi")
        assert result2.filter.state == ThinkState.INSIDE_THINK
        
        result3 = feed_think_filter(result2.filter, "nk>")
        assert result3.filter.state == ThinkState.OUTSIDE_THINK


class TestThinkFilterValidation:
    """Validation tests for ThinkFilter dataclass."""

    def test_think_filter_invalid_state_raises_error(self):
        """Test invalid state type raises TypeError."""
        with pytest.raises(TypeError, match="state must be ThinkState"):
            ThinkFilter(state="invalid", buffer="")  # type: ignore

    def test_think_filter_invalid_buffer_raises_error(self):
        """Test invalid buffer type raises TypeError."""
        with pytest.raises(TypeError, match="buffer must be str"):
            ThinkFilter(state=ThinkState.OUTSIDE_THINK, buffer=123)  # type: ignore


class TestBugDetection:
    """Bug detection tests for think filter."""

    def test_bug_partial_tag_may_not_be_handled_correctly(self):
        """BUG: Partial tags may not be handled correctly."""
        # Very long partial tags may cause buffer issues
        # This test documents the potential issue
        # TODO: Add test with very long partial tags

    def test_bug_nested_think_blocks_may_cause_state_confusion(self):
        """BUG: Nested think blocks may cause state confusion."""
        # Nested blocks may not transition state correctly
        # This test documents the potential issue
        # TODO: Add test with nested think blocks

    def test_bug_buffer_may_grow_unbounded(self):
        """BUG: Buffer may grow unbounded with malformed input."""
        # Malformed input without closing tags may cause buffer to grow
        # This test documents the potential issue
        # TODO: Add test with very long unclosed think block

    def test_bug_case_sensitivity_may_not_be_handled(self):
        """BUG: Case sensitivity may not be handled."""
        # <THINK> vs <think> may not be handled correctly
        # This test documents the potential issue
        # TODO: Add test with case variations

    def test_bug_unicode_in_tags_may_cause_issues(self):
        """BUG: Unicode in tags may cause parsing issues."""
        # Unicode characters in think blocks may cause issues
        # This test documents the potential issue
        # TODO: Add test with Unicode characters
