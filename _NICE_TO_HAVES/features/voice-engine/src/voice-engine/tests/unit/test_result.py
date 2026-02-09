"""
Deep comprehensive tests for Result type (Ok/Err) and error handling.

Tests Result type operations, error handling, ChatError, and bug detection.
"""
import pytest
from toolbox.llm.result import (
    Result,
    Ok,
    Err,
    ChatError,
    ChatErrorCode,
    ChatResult,
    make_error,
    err,
)


class TestOk:
    """Deep comprehensive tests for Ok variant."""

    def test_ok_creation(self):
        """Test creating Ok value."""
        result: Result[int, str] = Ok(42)
        assert result.value == 42

    def test_ok_is_ok(self):
        """Test is_ok returns True."""
        result = Ok(42)
        assert result.is_ok() is True

    def test_ok_is_err(self):
        """Test is_err returns False."""
        result = Ok(42)
        assert result.is_err() is False

    def test_ok_unwrap(self):
        """Test unwrap returns value."""
        result = Ok(42)
        assert result.unwrap() == 42

    def test_ok_unwrap_or(self):
        """Test unwrap_or returns value (ignores default)."""
        result = Ok(42)
        assert result.unwrap_or(0) == 42

    def test_ok_unwrap_err_raises_error(self):
        """Test unwrap_err raises ValueError."""
        result = Ok(42)
        with pytest.raises(ValueError, match="Called unwrap_err on Ok"):
            result.unwrap_err()

    def test_ok_map(self):
        """Test map applies function."""
        result: Result[int, str] = Ok(42)
        mapped = result.map(lambda x: x * 2)
        assert mapped.is_ok()
        assert mapped.unwrap() == 84

    def test_ok_map_err(self):
        """Test map_err returns self unchanged."""
        result: Result[int, str] = Ok(42)
        mapped = result.map_err(lambda e: f"Error: {e}")
        assert mapped.is_ok()
        assert mapped.unwrap() == 42

    def test_ok_and_then(self):
        """Test and_then chains operations."""
        result: Result[int, str] = Ok(42)
        chained = result.and_then(lambda x: Ok(x * 2))
        assert chained.is_ok()
        assert chained.unwrap() == 84

    def test_ok_and_then_returns_error(self):
        """Test and_then can return error."""
        result: Result[int, str] = Ok(42)
        chained = result.and_then(lambda x: Err("error"))
        assert chained.is_err()
        assert chained.unwrap_err() == "error"

    def test_ok_or_else(self):
        """Test or_else returns self unchanged."""
        result: Result[int, str] = Ok(42)
        result_or = result.or_else(lambda e: Ok(0))
        assert result_or.is_ok()
        assert result_or.unwrap() == 42

    def test_ok_with_different_types(self):
        """Test Ok with different value types."""
        ok_int = Ok(42)
        ok_str = Ok("hello")
        ok_list = Ok([1, 2, 3])
        ok_none = Ok(None)
        
        assert ok_int.unwrap() == 42
        assert ok_str.unwrap() == "hello"
        assert ok_list.unwrap() == [1, 2, 3]
        assert ok_none.unwrap() is None


class TestErr:
    """Deep comprehensive tests for Err variant."""

    def test_err_creation(self):
        """Test creating Err value."""
        result: Result[int, str] = Err("error")
        assert result.error == "error"

    def test_err_is_ok(self):
        """Test is_ok returns False."""
        result = Err("error")
        assert result.is_ok() is False

    def test_err_is_err(self):
        """Test is_err returns True."""
        result = Err("error")
        assert result.is_err() is True

    def test_err_unwrap_raises_error(self):
        """Test unwrap raises ValueError."""
        result = Err("error")
        with pytest.raises(ValueError, match="Called unwrap on Err"):
            result.unwrap()

    def test_err_unwrap_or(self):
        """Test unwrap_or returns default."""
        result: Result[int, str] = Err("error")
        assert result.unwrap_or(0) == 0

    def test_err_unwrap_err(self):
        """Test unwrap_err returns error."""
        result = Err("error")
        assert result.unwrap_err() == "error"

    def test_err_map(self):
        """Test map returns self unchanged."""
        result: Result[int, str] = Err("error")
        mapped = result.map(lambda x: x * 2)
        assert mapped.is_err()
        assert mapped.unwrap_err() == "error"

    def test_err_map_err(self):
        """Test map_err applies function."""
        result: Result[int, str] = Err("error")
        mapped = result.map_err(lambda e: f"Error: {e}")
        assert mapped.is_err()
        assert mapped.unwrap_err() == "Error: error"

    def test_err_and_then(self):
        """Test and_then returns self unchanged."""
        result: Result[int, str] = Err("error")
        chained = result.and_then(lambda x: Ok(x * 2))
        assert chained.is_err()
        assert chained.unwrap_err() == "error"

    def test_err_or_else(self):
        """Test or_else applies function."""
        result: Result[int, str] = Err("error")
        result_or = result.or_else(lambda e: Ok(0))
        assert result_or.is_ok()
        assert result_or.unwrap() == 0

    def test_err_with_different_types(self):
        """Test Err with different error types."""
        err_str = Err("error")
        err_int = Err(404)
        err_dict = Err({"code": "error"})
        
        assert err_str.unwrap_err() == "error"
        assert err_int.unwrap_err() == 404
        assert err_dict.unwrap_err() == {"code": "error"}


class TestResultChaining:
    """Tests for Result method chaining."""

    def test_chain_multiple_operations(self):
        """Test chaining multiple operations."""
        result: Result[int, str] = Ok(10)
        final = (
            result
            .map(lambda x: x * 2)
            .and_then(lambda x: Ok(x + 5) if x < 30 else Err("too large"))
            .map(lambda x: x - 1)
        )
        assert final.is_ok()
        assert final.unwrap() == 24

    def test_chain_with_error(self):
        """Test chaining stops at first error."""
        result: Result[int, str] = Ok(10)
        final = (
            result
            .map(lambda x: x * 2)
            .and_then(lambda x: Err("error"))
            .map(lambda x: x + 5)  # Should not execute
        )
        assert final.is_err()
        assert final.unwrap_err() == "error"

    def test_chain_error_recovery(self):
        """Test error recovery in chain."""
        result: Result[int, str] = Err("initial error")
        final = (
            result
            .or_else(lambda e: Ok(42))
            .map(lambda x: x * 2)
        )
        assert final.is_ok()
        assert final.unwrap() == 84


class TestChatErrorCode:
    """Deep comprehensive tests for ChatErrorCode enum."""

    def test_all_error_codes_exist(self):
        """Test all error codes are defined."""
        assert ChatErrorCode.CONVERSATION_NOT_FOUND
        assert ChatErrorCode.CONVERSATION_NOT_ACTIVE
        assert ChatErrorCode.MESSAGE_TOO_LONG
        assert ChatErrorCode.MESSAGE_EMPTY
        assert ChatErrorCode.INJECTION_DETECTED
        assert ChatErrorCode.OUTPUT_FILTERED
        assert ChatErrorCode.LLM_NOT_CONFIGURED
        assert ChatErrorCode.LLM_TIMEOUT
        assert ChatErrorCode.CONTEXT_WINDOW_EXCEEDED

    def test_error_code_values(self):
        """Test error code string values."""
        assert ChatErrorCode.CONVERSATION_NOT_FOUND.value == "conversation_not_found"
        assert ChatErrorCode.MESSAGE_TOO_LONG.value == "message_too_long"
        assert ChatErrorCode.INJECTION_DETECTED.value == "injection_detected"


class TestChatError:
    """Deep comprehensive tests for ChatError dataclass."""

    def test_chat_error_creation(self):
        """Test creating ChatError."""
        error = ChatError(
            code=ChatErrorCode.MESSAGE_TOO_LONG,
            message="Message too long",
        )
        assert error.code == ChatErrorCode.MESSAGE_TOO_LONG
        assert error.message == "Message too long"
        assert error.details == ()
        assert error.timestamp != ""

    def test_chat_error_with_details(self):
        """Test ChatError with details."""
        error = ChatError(
            code=ChatErrorCode.MESSAGE_TOO_LONG,
            message="Message too long",
            details=(("length", 150000), ("max", 100000)),
        )
        assert len(error.details) == 2
        assert error.details[0] == ("length", 150000)

    def test_chat_error_timestamp_auto_set(self):
        """Test ChatError timestamp is auto-set."""
        error = ChatError(
            code=ChatErrorCode.MESSAGE_TOO_LONG,
            message="Message too long",
        )
        assert error.timestamp != ""
        # Should be ISO format
        assert "T" in error.timestamp or error.timestamp.count("-") >= 2

    def test_chat_error_custom_timestamp(self):
        """Test ChatError with custom timestamp."""
        custom_time = "2024-01-01T00:00:00Z"
        error = ChatError(
            code=ChatErrorCode.MESSAGE_TOO_LONG,
            message="Message too long",
            timestamp=custom_time,
        )
        assert error.timestamp == custom_time

    def test_chat_error_to_dict(self):
        """Test ChatError to_dict conversion."""
        error = ChatError(
            code=ChatErrorCode.MESSAGE_TOO_LONG,
            message="Message too long",
            details=(("length", 150000), ("max", 100000)),
            timestamp="2024-01-01T00:00:00Z",
        )
        error_dict = error.to_dict()
        assert error_dict["code"] == "message_too_long"
        assert error_dict["message"] == "Message too long"
        assert error_dict["details"]["length"] == 150000
        assert error_dict["details"]["max"] == 100000
        assert error_dict["timestamp"] == "2024-01-01T00:00:00Z"

    def test_chat_error_frozen(self):
        """Test ChatError is frozen (immutable)."""
        error = ChatError(
            code=ChatErrorCode.MESSAGE_TOO_LONG,
            message="Message too long",
        )
        # Should not be able to modify
        with pytest.raises(Exception):  # Frozen dataclass raises
            error.message = "Modified"  # type: ignore


class TestMakeError:
    """Deep comprehensive tests for make_error function."""

    def test_make_error_basic(self):
        """Test make_error creates ChatError."""
        error = make_error(
            ChatErrorCode.MESSAGE_TOO_LONG,
            "Message too long",
        )
        assert isinstance(error, ChatError)
        assert error.code == ChatErrorCode.MESSAGE_TOO_LONG
        assert error.message == "Message too long"

    def test_make_error_with_details(self):
        """Test make_error with keyword details."""
        error = make_error(
            ChatErrorCode.MESSAGE_TOO_LONG,
            "Message too long",
            length=150000,
            max=100000,
        )
        assert len(error.details) == 2
        details_dict = dict(error.details)
        assert details_dict["length"] == 150000
        assert details_dict["max"] == 100000

    def test_make_error_multiple_details(self):
        """Test make_error with multiple details."""
        error = make_error(
            ChatErrorCode.INJECTION_DETECTED,
            "Injection detected",
            pattern="ignore",
            risk="high",
            count=3,
        )
        assert len(error.details) == 3


class TestErrHelper:
    """Deep comprehensive tests for err helper function."""

    def test_err_creates_err_result(self):
        """Test err creates Err[ChatError]."""
        result = err(
            ChatErrorCode.MESSAGE_TOO_LONG,
            "Message too long",
        )
        assert isinstance(result, Err)
        assert result.is_err()
        error = result.unwrap_err()
        assert isinstance(error, ChatError)
        assert error.code == ChatErrorCode.MESSAGE_TOO_LONG

    def test_err_with_details(self):
        """Test err with details."""
        result = err(
            ChatErrorCode.MESSAGE_TOO_LONG,
            "Message too long",
            length=150000,
            max=100000,
        )
        error = result.unwrap_err()
        assert len(error.details) == 2


class TestResultPatternMatching:
    """Tests for Result pattern matching (Python 3.10+)."""

    def test_match_ok(self):
        """Test pattern matching with Ok."""
        result: Result[int, str] = Ok(42)
        match result:
            case Ok(value):
                assert value == 42
            case Err(_):
                pytest.fail("Should match Ok")

    def test_match_err(self):
        """Test pattern matching with Err."""
        result: Result[int, str] = Err("error")
        match result:
            case Ok(_):
                pytest.fail("Should match Err")
            case Err(error):
                assert error == "error"

    def test_match_chat_result(self):
        """Test pattern matching with ChatResult."""
        result: ChatResult[int] = err(
            ChatErrorCode.MESSAGE_TOO_LONG,
            "Message too long",
        )
        match result:
            case Ok(_):
                pytest.fail("Should match Err")
            case Err(error):
                assert isinstance(error, ChatError)
                assert error.code == ChatErrorCode.MESSAGE_TOO_LONG


class TestBugDetection:
    """Bug detection tests for Result type."""

    def test_bug_unwrap_may_not_provide_context(self):
        """BUG: unwrap may not provide enough context in error message."""
        # Error messages may not include value/error details
        # This test documents the potential issue
        # TODO: Add test to verify error message context

    def test_bug_map_may_not_preserve_type(self):
        """BUG: map may not preserve generic types correctly."""
        # Type inference may be lost after map
        # This test documents the potential issue
        # TODO: Add test with type checking

    def test_bug_chat_error_details_may_not_be_serializable(self):
        """BUG: ChatError details may not be JSON serializable."""
        # Complex types in details may not serialize
        # This test documents the potential issue
        # TODO: Add test with non-serializable details

    def test_bug_frozen_dataclass_may_not_work_with_inheritance(self):
        """BUG: Frozen ChatError may not work with inheritance."""
        # Frozen dataclass may cause issues if extended
        # This test documents the potential issue
        # TODO: Add test with inheritance
