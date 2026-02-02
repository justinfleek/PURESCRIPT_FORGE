"""
Effect Decorators - Idempotent and Monotonic Function Markers

Provides decorators for marking functions with specific mathematical properties:
- idempotent: f(f(x)) = f(x) - applying twice is same as once
- monotonic: Preserves ordering - increasing or decreasing

These are used for:
- Documentation and type safety
- Optimization opportunities
- Property-based testing
- Formal verification

IMPLEMENTATION:
    Decorators are currently pass-through (no runtime enforcement).
    In production, these could:
    - Cache results for idempotent functions
    - Validate monotonicity in tests
    - Enable compiler optimizations
"""

from functools import wraps
from typing import Callable, TypeVar, ParamSpec

P = ParamSpec("P")
T = TypeVar("T")
R = TypeVar("R")


def idempotent(func: Callable[P, R]) -> Callable[P, R]:
    """
    Mark function as idempotent: f(f(x)) = f(x).
    
    Idempotent functions can be safely called multiple times
    without changing the result after the first call.
    
    Examples:
        - normalize_text("  hello  ") -> "hello" (idempotent)
        - sort_list([3,1,2]) -> [1,2,3] (idempotent)
        - increment_counter(x) -> x+1 (NOT idempotent)
    
    Usage:
        @idempotent
        def normalize_query(query: str) -> str:
            return query.strip().lower()
    
    PROPERTY: For all x, f(f(x)) == f(x)
    """
    func.__idempotent__ = True  # type: ignore[attr-defined]
    return func


class MonotonicDirection:
    """Monotonic direction constants."""
    INCREASING = "increasing"
    DECREASING = "decreasing"


def monotonic(direction: str = MonotonicDirection.INCREASING):
    """
    Mark function as monotonic (preserves ordering).
    
    Monotonic functions preserve the ordering of their inputs:
    - Increasing: if x < y, then f(x) <= f(y)
    - Decreasing: if x < y, then f(y) <= f(x)
    
    Examples:
        - log(x) is increasing monotonic
        - -x is decreasing monotonic
        - x^2 is NOT monotonic (negative vs positive)
    
    Usage:
        @monotonic(MonotonicDirection.INCREASING)
        def calculate_score(engagement: float) -> float:
            return engagement * 10.0
    
    PROPERTY:
        Increasing: for all x, y: x < y => f(x) <= f(y)
        Decreasing: for all x, y: x < y => f(y) <= f(x)
    """
    def decorator(func: Callable[P, R]) -> Callable[P, R]:
        func.__monotonic__ = True  # type: ignore[attr-defined]
        func.__monotonic_direction__ = direction  # type: ignore[attr-defined]
        return func
    return decorator


__all__ = ["idempotent", "monotonic", "MonotonicDirection"]
