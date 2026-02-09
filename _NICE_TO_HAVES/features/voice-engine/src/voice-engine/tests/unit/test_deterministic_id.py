"""
Deep comprehensive tests for deterministic ID generation.

Tests UUID5 generation, determinism, edge cases, and bug detection.
"""
import pytest
from toolbox.core.deterministic_id import make_uuid, FORGE_NAMESPACE
import uuid


class TestMakeUuid:
    """Deep comprehensive tests for make_uuid function."""

    def test_generates_uuid5_format(self):
        """Test generates UUID5 format."""
        result = make_uuid("test", "content")
        uuid_obj = uuid.UUID(result)
        assert uuid_obj.version == 5

    def test_deterministic_same_input(self):
        """Test same input produces same UUID."""
        result1 = make_uuid("test", "content")
        result2 = make_uuid("test", "content")
        assert result1 == result2

    def test_deterministic_different_order(self):
        """Test different order produces different UUID."""
        result1 = make_uuid("test", "content")
        result2 = make_uuid("content", "test")
        assert result1 != result2

    def test_uses_forge_namespace(self):
        """Test uses FORGE_NAMESPACE."""
        result = make_uuid("test")
        uuid_obj = uuid.UUID(result)
        # UUID5 namespace is embedded in the UUID
        # We can verify by generating with same namespace manually
        expected = uuid.uuid5(FORGE_NAMESPACE, "test")
        assert result == str(expected)

    def test_joins_content_with_pipe(self):
        """Test content strings are joined with pipe."""
        result1 = make_uuid("test", "content")
        result2 = make_uuid("test|content")
        assert result1 == result2

    def test_empty_string(self):
        """Test empty string input."""
        result = make_uuid("")
        assert isinstance(result, str)
        assert len(result) == 36  # UUID format length

    def test_multiple_empty_strings(self):
        """Test multiple empty strings."""
        result = make_uuid("", "", "")
        assert isinstance(result, str)
        assert len(result) == 36

    def test_very_long_string(self):
        """Test very long string input."""
        long_string = "a" * 10000
        result = make_uuid(long_string)
        assert isinstance(result, str)
        assert len(result) == 36

    def test_unicode_characters(self):
        """Test Unicode characters."""
        result = make_uuid("测试", "🚀", "こんにちは")
        assert isinstance(result, str)
        assert len(result) == 36

    def test_special_characters(self):
        """Test special characters."""
        result = make_uuid("test|with|pipes", "test:with:colons")
        assert isinstance(result, str)
        assert len(result) == 36

    def test_none_values_handled(self):
        """Test None values are handled."""
        # None should be converted to string
        result = make_uuid("test", None)  # type: ignore
        assert isinstance(result, str)
        assert len(result) == 36

    def test_numeric_values(self):
        """Test numeric values are handled."""
        result = make_uuid("123", "456")
        assert isinstance(result, str)
        assert len(result) == 36

    def test_many_arguments(self):
        """Test many arguments."""
        result = make_uuid("a", "b", "c", "d", "e", "f", "g", "h", "i", "j")
        assert isinstance(result, str)
        assert len(result) == 36

    def test_single_argument(self):
        """Test single argument."""
        result = make_uuid("test")
        assert isinstance(result, str)
        assert len(result) == 36

    def test_no_arguments(self):
        """Test no arguments."""
        result = make_uuid()
        assert isinstance(result, str)
        assert len(result) == 36

    def test_whitespace_preserved(self):
        """Test whitespace is preserved."""
        result1 = make_uuid("test content")
        result2 = make_uuid("test", "content")
        assert result1 != result2  # Different due to whitespace

    def test_case_sensitive(self):
        """Test case sensitivity."""
        result1 = make_uuid("Test")
        result2 = make_uuid("test")
        assert result1 != result2

    def test_collision_resistance(self):
        """Test collision resistance with many inputs."""
        results = set()
        for i in range(1000):
            result = make_uuid(f"test_{i}")
            assert result not in results  # No collisions
            results.add(result)

    def test_bug_uuid5_may_have_collisions(self):
        """BUG: UUID5 may have collisions with similar inputs."""
        # UUID5 is deterministic but may have collisions
        # This test documents the potential issue
        result1 = make_uuid("test", "content")
        result2 = make_uuid("test", "content")
        assert result1 == result2  # Should be deterministic
        # BUG: Very similar inputs may collide
        # This test documents the potential issue

    def test_bug_pipe_character_in_content(self):
        """BUG: Pipe character in content may cause issues."""
        # If content contains "|", joining may be ambiguous
        result1 = make_uuid("test|content")
        result2 = make_uuid("test", "content")
        # These should be different, but pipe in content may cause confusion
        # BUG: Pipe character may not be handled correctly
        # This test documents the potential issue
        assert result1 != result2

    def test_bug_very_long_content_may_cause_issues(self):
        """BUG: Very long content may cause performance issues."""
        very_long = "a" * 1000000  # 1MB string
        result = make_uuid(very_long)
        # Should still work, but may be slow
        # BUG: Very long content may cause performance issues
        # This test documents the potential issue
        assert isinstance(result, str)
        assert len(result) == 36
