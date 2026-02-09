"""
╔══════════════════════════════════════════════════════════════════════════════╗
║                         Result Type - Error Handling                          ║
║                                                                              ║
║  Algebraic Data Type for explicit error handling.                            ║
║                                                                              ║
║  Instead of exceptions (which are implicit control flow) or None             ║
║  (which loses error information), we use Result[T, E] which is               ║
║  either Ok(value) or Err(error).                                             ║
║                                                                              ║
║  HASKELL EQUIVALENT:                                                         ║
║    data Either a b = Left a | Right b                                        ║
║    type Result e a = Either e a                                              ║
║                                                                              ║
║  RUST EQUIVALENT:                                                            ║
║    enum Result<T, E> { Ok(T), Err(E) }                                       ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝

WHY RESULT TYPES?

    1. EXPLICIT ERROR HANDLING
       Every function that can fail declares it in its type signature.
       You can't forget to handle errors because the type system reminds you.

    2. NO HIDDEN CONTROL FLOW
       Exceptions can jump to any catch block up the stack.
       Result forces you to handle errors at each call site.

    3. COMPOSABLE
       Results can be chained with map, flat_map, and_then, etc.
       This enables railway-oriented programming.

    4. ERROR INFORMATION PRESERVED
       Unlike returning None, Err contains the full error with context.

USAGE:
    from toolbox.llm.result import Result, Ok, Err, ChatError

    def divide(a: int, b: int) -> Result[float, str]:
        if b == 0:
            return Err("division by zero")
        return Ok(a / b)

    # Pattern matching (Python 3.10+)
    match divide(10, 2):
        case Ok(value):
            print(f"Result: {value}")
        case Err(error):
            print(f"Error: {error}")

    # Method chaining
    result = (
        divide(10, 2)
        .map(lambda x: x * 2)
        .and_then(lambda x: Ok(int(x)) if x < 100 else Err("too large"))
    )

TESTING:
    pytest tests/unit/test_result.py -v
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from datetime import timezone, datetime
from enum import Enum
from typing import Generic, TypeVar


# Type variables for Result
T = TypeVar("T")  # Success value type
E = TypeVar("E")  # Error type
U = TypeVar("U")  # Transformed success type
F = TypeVar("F")  # Transformed error type


# =============================================================================
# § 1. RESULT TYPE
# =============================================================================


@dataclass(frozen=True, slots=True)
class Ok(Generic[T]):
    """
    Success variant of Result.

    Contains a value of type T.

    Example:
        result: Result[int, str] = Ok(42)
        assert result.is_ok()
        assert result.unwrap() == 42
    """

    value: T

    def is_ok(self) -> bool:
        """Return True (this is Ok)."""
        return True

    def is_err(self) -> bool:
        """Return False (this is not Err)."""
        return False

    def unwrap(self) -> T:
        """Return the contained value."""
        return self.value

    def unwrap_or(self, default: T) -> T:
        """Return the contained value (ignoring default)."""
        return self.value

    def unwrap_err(self) -> None:
        """Raise because this is Ok, not Err."""
        raise ValueError("Called unwrap_err on Ok")

    def map(self, f: Callable[[T], U]) -> Ok[U]:
        """Apply f to the contained value."""
        return Ok(f(self.value))

    def map_err(self, f: Callable[[E], F]) -> Ok[T]:
        """Return self unchanged (no error to map)."""
        return self

    def and_then(self, f: Callable[[T], Result[U, E]]) -> Result[U, E]:
        """Apply f to the contained value, returning the result."""
        return f(self.value)

    def or_else(self, f: Callable[[E], Result[T, F]]) -> Ok[T]:
        """Return self unchanged (no error to handle)."""
        return self


@dataclass(frozen=True, slots=True)
class Err(Generic[E]):
    """
    Error variant of Result.

    Contains an error of type E.

    Example:
        result: Result[int, str] = Err("division by zero")
        assert result.is_err()
        assert result.unwrap_err() == "division by zero"
    """

    error: E

    def is_ok(self) -> bool:
        """Return False (this is not Ok)."""
        return False

    def is_err(self) -> bool:
        """Return True (this is Err)."""
        return True

    def unwrap(self) -> None:
        """Raise because this is Err, not Ok."""
        raise ValueError(f"Called unwrap on Err: {self.error}")

    def unwrap_or(self, default: T) -> T:
        """Return the default value."""
        return default

    def unwrap_err(self) -> E:
        """Return the contained error."""
        return self.error

    def map(self, f: Callable[[T], U]) -> Err[E]:
        """Return self unchanged (no value to map)."""
        return self

    def map_err(self, f: Callable[[E], F]) -> Err[F]:
        """Apply f to the contained error."""
        return Err(f(self.error))

    def and_then(self, f: Callable[[T], Result[U, E]]) -> Err[E]:
        """Return self unchanged (no value to chain)."""
        return self

    def or_else(self, f: Callable[[E], Result[T, F]]) -> Result[T, F]:
        """Apply f to the contained error, returning the result."""
        return f(self.error)


# Union type for Result
Result = Ok[T] | Err[E]


# =============================================================================
# § 2. CHAT ERROR TYPES
# =============================================================================
"""
Structured error types for the chat system.

Each error type contains:
1. A unique code (for programmatic handling)
2. A human-readable message
3. Optional details for debugging
4. A timestamp for logging

ERROR HANDLING PATTERN:
    ```haskell
    data ChatError 
        = ConversationNotFound ConvId
        | MessageTooLong Int Int  -- actual, max
        | InjectionDetected [Pattern]
        | OutputFiltered FilterResult
        | LLMError LLMErrorCode String
    ```
"""


class ChatErrorCode(Enum):
    """
    Standardized error codes for chat operations.

    NAMING CONVENTION:
        - Use snake_case
        - Be specific (not just "error")
        - Include the subject (conversation, message, etc.)

    ERROR CODE CATEGORIES:
        - conversation_*: Conversation-related errors
        - message_*: Message validation errors
        - security_*: Security/safety violations
        - llm_*: LLM provider errors
        - config_*: Configuration errors
    """

    # Conversation errors
    CONVERSATION_NOT_FOUND = "conversation_not_found"
    CONVERSATION_NOT_ACTIVE = "conversation_not_active"
    CONVERSATION_ARCHIVED = "conversation_archived"

    # Message errors
    MESSAGE_TOO_LONG = "message_too_long"
    MESSAGE_EMPTY = "message_empty"
    INVALID_MESSAGE_ROLE = "invalid_message_role"

    # Security errors
    INJECTION_DETECTED = "injection_detected"
    OUTPUT_FILTERED = "output_filtered"
    RATE_LIMITED = "rate_limited"

    # LLM errors
    LLM_NOT_CONFIGURED = "llm_not_configured"
    LLM_TIMEOUT = "llm_timeout"
    LLM_ERROR = "llm_error"
    CONTEXT_WINDOW_EXCEEDED = "context_window_exceeded"

    # Configuration errors
    BRAND_VOICE_NOT_FOUND = "brand_voice_not_found"
    ANALYST_NOT_FOUND = "analyst_not_found"


@dataclass(frozen=True, slots=True)
class ChatError:
    """
    Structured error for chat operations.

    IMMUTABLE: Errors are frozen dataclasses - they cannot be modified
    after creation. This ensures error information is preserved exactly.

    Example:
        error = ChatError(
            code=ChatErrorCode.MESSAGE_TOO_LONG,
            message="Message exceeds maximum length",
            details={"length": 150000, "max": 100000},
        )
    """

    code: ChatErrorCode
    message: str
    details: tuple[tuple[str, str | int | float | bool], ...] = ()
    timestamp: str = ""

    def __post_init__(self) -> None:
        """Set timestamp if not provided."""
        if not self.timestamp:
            # Use object.__setattr__ because dataclass is frozen
            object.__setattr__(self, "timestamp", datetime.now(timezone.utc).isoformat())

    def to_dict(self) -> dict[str, str | dict[str, str | int | float | bool]]:
        """Convert to dictionary for JSON serialization."""
        return {
            "code": self.code.value,
            "message": self.message,
            "details": dict(self.details),
            "timestamp": self.timestamp,
        }


# Type alias for chat operation results
ChatResult = Result[T, ChatError]


# =============================================================================
# § 3. HELPER FUNCTIONS
# =============================================================================


def make_error(
    code: ChatErrorCode,
    message: str,
    **details: str | float | bool,
) -> ChatError:
    """
    Create a ChatError with the given code, message, and details.

    Example:
        error = make_error(
            ChatErrorCode.MESSAGE_TOO_LONG,
            "Message exceeds maximum length",
            length=150000,
            max=100000,
        )
    """
    return ChatError(
        code=code,
        message=message,
        details=tuple(details.items()),
    )


def err(
    code: ChatErrorCode,
    message: str,
    **details: str | float | bool,
) -> Err[ChatError]:
    """
    Create an Err containing a ChatError.

    Shorthand for Err(make_error(...)).

    Example:
        def validate_message(content: str) -> ChatResult[str]:
            if len(content) > 100000:
                return err(
                    ChatErrorCode.MESSAGE_TOO_LONG,
                    "Message too long",
                    length=len(content),
                )
            return Ok(content)
    """
    return Err(make_error(code, message, **details))


# =============================================================================
# EXPORTS
# =============================================================================
__all__ = [
    # Core types
    "Result",
    "Ok",
    "Err",
    # Chat-specific
    "ChatError",
    "ChatErrorCode",
    "ChatResult",
    # Helpers
    "make_error",
    "err",
]
