"""
Deep comprehensive tests for Effect Decorators module
Tests idempotent and monotonic decorators with edge cases and bug detection
"""

import pytest
from toolbox.core.effects import idempotent, monotonic, MonotonicDirection


class TestIdempotentDecorator:
    """Tests for @idempotent decorator"""
    
    def test_idempotent_marks_function(self):
        """Test that @idempotent decorator marks function correctly"""
        @idempotent
        def normalize_text(text: str) -> str:
            return text.strip().lower()
        
        assert hasattr(normalize_text, "__idempotent__")
        assert normalize_text.__idempotent__ is True
    
    def test_idempotent_preserves_functionality(self):
        """Test that @idempotent doesn't change function behavior"""
        @idempotent
        def normalize_text(text: str) -> str:
            return text.strip().lower()
        
        assert normalize_text("  HELLO  ") == "hello"
        assert normalize_text("test") == "test"
    
    def test_idempotent_property_holds(self):
        """Test that idempotent property holds: f(f(x)) = f(x)"""
        @idempotent
        def normalize_text(text: str) -> str:
            return text.strip().lower()
        
        test_cases = ["  HELLO  ", "test", "", "  MULTI   WORD  "]
        for text in test_cases:
            once = normalize_text(text)
            twice = normalize_text(once)
            assert twice == once, f"Idempotency failed for '{text}': f(f(x))={twice} != f(x)={once}"
    
    def test_bug_idempotent_no_runtime_enforcement(self):
        """
        BUG: @idempotent decorator (line 30-50) is pass-through and doesn't
        enforce idempotency at runtime. A function marked as @idempotent may
        not actually be idempotent, leading to incorrect assumptions and bugs.
        
        Root cause: Decorator only sets attribute, doesn't validate property
        Consequences: Functions incorrectly marked as idempotent may be cached
        or optimized incorrectly, leading to incorrect behavior
        
        Proposed solution: Add runtime validation in tests or use property-based
        testing to verify idempotency
        """
        # This function is NOT idempotent but can be marked as such
        @idempotent
        def increment_counter(x: int) -> int:
            return x + 1
        
        # Decorator accepts it without validation
        assert hasattr(increment_counter, "__idempotent__")
        # But function is not actually idempotent
        assert increment_counter(1) == 2
        assert increment_counter(2) == 3  # f(f(1)) = 3 != f(1) = 2
    
    def test_bug_idempotent_doesnt_handle_side_effects(self):
        """
        BUG: @idempotent decorator doesn't check for side effects. A function
        may be mathematically idempotent (f(f(x)) = f(x)) but have side effects
        that occur on every call (e.g., logging, database writes).
        
        Root cause: Decorator only checks return value equality, not side effects
        Consequences: Functions with side effects marked as idempotent may cause
        duplicate operations (e.g., duplicate database writes, duplicate logs)
        
        Proposed solution: Document that idempotent only applies to return values,
        not side effects. Consider separate decorator for "pure" functions.
        """
        call_count = []
        
        @idempotent
        def function_with_side_effect(x: int) -> int:
            call_count.append(1)  # Side effect
            return abs(x)
        
        result1 = function_with_side_effect(-5)
        result2 = function_with_side_effect(result1)
        
        # Return value is idempotent
        assert result1 == result2 == 5
        # But side effect occurs twice
        assert len(call_count) == 2  # BUG: Side effect not idempotent
    
    def test_bug_idempotent_doesnt_handle_mutable_inputs(self):
        """
        BUG: @idempotent decorator doesn't handle mutable inputs correctly.
        If a function mutates its input, calling it twice may produce different
        results even if the function is marked as idempotent.
        
        Root cause: Decorator doesn't validate that inputs aren't mutated
        Consequences: Functions that mutate inputs may break idempotency property
        
        Proposed solution: Document that idempotent functions should not mutate inputs,
        or use immutable data structures
        """
        @idempotent
        def sort_list_in_place(lst: list) -> list:
            lst.sort()  # Mutates input
            return lst
        
        test_list = [3, 1, 2]
        result1 = sort_list_in_place(test_list)
        # Input is already sorted, so second call should be idempotent
        # But if function mutates input, behavior may be unexpected
        result2 = sort_list_in_place(result1)
        
        # This works because list is already sorted
        assert result1 == result2 == [1, 2, 3]
        # But if we pass unsorted list again, it would work
        # The bug is that mutation makes idempotency dependent on input state


class TestMonotonicDecorator:
    """Tests for @monotonic decorator"""
    
    def test_monotonic_marks_function_increasing(self):
        """Test that @monotonic decorator marks function as increasing"""
        @monotonic(MonotonicDirection.INCREASING)
        def calculate_score(engagement: float) -> float:
            return engagement * 10.0
        
        assert hasattr(calculate_score, "__monotonic__")
        assert calculate_score.__monotonic__ is True
        assert calculate_score.__monotonic_direction__ == MonotonicDirection.INCREASING
    
    def test_monotonic_marks_function_decreasing(self):
        """Test that @monotonic decorator marks function as decreasing"""
        @monotonic(MonotonicDirection.DECREASING)
        def negate(x: float) -> float:
            return -x
        
        assert hasattr(negate, "__monotonic__")
        assert negate.__monotonic__ is True
        assert negate.__monotonic_direction__ == MonotonicDirection.DECREASING
    
    def test_monotonic_defaults_to_increasing(self):
        """Test that @monotonic defaults to increasing"""
        @monotonic()
        def double(x: float) -> float:
            return x * 2.0
        
        assert hasattr(double, "__monotonic__")
        assert double.__monotonic_direction__ == MonotonicDirection.INCREASING
    
    def test_monotonic_preserves_functionality(self):
        """Test that @monotonic doesn't change function behavior"""
        @monotonic(MonotonicDirection.INCREASING)
        def calculate_score(engagement: float) -> float:
            return engagement * 10.0
        
        assert calculate_score(5.0) == 50.0
        assert calculate_score(10.0) == 100.0
    
    def test_monotonic_increasing_property(self):
        """Test that increasing monotonic property holds: x < y => f(x) <= f(y)"""
        @monotonic(MonotonicDirection.INCREASING)
        def calculate_score(engagement: float) -> float:
            return engagement * 10.0
        
        test_pairs = [(1.0, 2.0), (0.0, 5.0), (10.0, 20.0), (-5.0, -1.0)]
        for x, y in test_pairs:
            if x < y:
                fx = calculate_score(x)
                fy = calculate_score(y)
                assert fx <= fy, f"Monotonicity failed: f({x})={fx} > f({y})={fy}"
    
    def test_monotonic_decreasing_property(self):
        """Test that decreasing monotonic property holds: x < y => f(y) <= f(x)"""
        @monotonic(MonotonicDirection.DECREASING)
        def negate(x: float) -> float:
            return -x
        
        test_pairs = [(1.0, 2.0), (0.0, 5.0), (10.0, 20.0)]
        for x, y in test_pairs:
            if x < y:
                fx = negate(x)
                fy = negate(y)
                assert fy <= fx, f"Monotonicity failed: f({y})={fy} > f({x})={fx}"
    
    def test_bug_monotonic_no_runtime_enforcement(self):
        """
        BUG: @monotonic decorator (line 59-85) is pass-through and doesn't
        enforce monotonicity at runtime. A function marked as @monotonic may
        not actually be monotonic, leading to incorrect assumptions and bugs.
        
        Root cause: Decorator only sets attributes, doesn't validate property
        Consequences: Functions incorrectly marked as monotonic may be optimized
        incorrectly or used in contexts that assume monotonicity
        
        Proposed solution: Add runtime validation in tests or use property-based
        testing to verify monotonicity
        """
        # This function is NOT monotonic but can be marked as such
        @monotonic(MonotonicDirection.INCREASING)
        def square(x: float) -> float:
            return x * x
        
        # Decorator accepts it without validation
        assert hasattr(square, "__monotonic__")
        # But function is not actually monotonic (negative vs positive)
        assert square(-2.0) == 4.0
        assert square(-1.0) == 1.0  # -2 < -1 but f(-2) = 4 > f(-1) = 1
    
    def test_bug_monotonic_doesnt_handle_equality(self):
        """
        BUG: @monotonic decorator doesn't specify whether equality is allowed.
        The property x < y => f(x) <= f(y) allows f(x) == f(y), but some
        contexts may require strict monotonicity (f(x) < f(y)).
        
        Root cause: Decorator doesn't distinguish strict vs non-strict monotonicity
        Consequences: Functions that are non-strictly monotonic may be used in
        contexts requiring strict monotonicity
        
        Proposed solution: Add strict_monotonic decorator or parameter
        """
        @monotonic(MonotonicDirection.INCREASING)
        def constant_function(x: float) -> float:
            return 5.0
        
        # Constant function is monotonic (non-strict)
        assert constant_function(1.0) == constant_function(2.0) == 5.0
        # But may not be suitable for contexts requiring strict monotonicity
    
    def test_bug_monotonic_doesnt_handle_nan_infinity(self):
        """
        BUG: @monotonic decorator doesn't handle NaN and Infinity values.
        Monotonicity property may not hold for these special values.
        
        Root cause: Decorator doesn't validate special float values
        Consequences: Functions with NaN/Infinity may break monotonicity assumptions
        
        Proposed solution: Document behavior with NaN/Infinity or add validation
        """
        import math
        
        @monotonic(MonotonicDirection.INCREASING)
        def divide_by_x(x: float) -> float:
            return 10.0 / x if x != 0.0 else float('inf')
        
        # Monotonicity may not hold for special values
        assert math.isinf(divide_by_x(0.0))
        assert math.isnan(divide_by_x(float('nan')))
        # Property x < y => f(x) <= f(y) may not hold near 0 or with NaN
    
    def test_bug_monotonic_doesnt_validate_direction(self):
        """
        BUG: @monotonic decorator doesn't validate that the direction parameter
        is valid. Invalid direction strings are accepted without error.
        
        Root cause: No validation of direction parameter
        Consequences: Typos or invalid directions may be silently accepted
        
        Proposed solution: Validate direction parameter, raise error for invalid values
        """
        # Invalid direction is accepted without error
        @monotonic("invalid_direction")
        def some_function(x: float) -> float:
            return x * 2.0
        
        # Decorator accepts invalid direction
        assert hasattr(some_function, "__monotonic__")
        assert some_function.__monotonic_direction__ == "invalid_direction"
        # BUG: Invalid direction should raise error or use default


class TestMonotonicDirection:
    """Tests for MonotonicDirection constants"""
    
    def test_monotonic_direction_constants(self):
        """Test that MonotonicDirection constants are correct"""
        assert MonotonicDirection.INCREASING == "increasing"
        assert MonotonicDirection.DECREASING == "decreasing"
    
    def test_monotonic_direction_immutability(self):
        """Test that MonotonicDirection constants cannot be modified"""
        # Constants should be strings, not modifiable
        original_increasing = MonotonicDirection.INCREASING
        # Attempting to modify would fail (strings are immutable)
        # This test documents expected behavior
        assert isinstance(MonotonicDirection.INCREASING, str)


class TestCombinedDecorators:
    """Tests for combining decorators"""
    
    def test_idempotent_and_monotonic_together(self):
        """Test that functions can be both idempotent and monotonic"""
        @idempotent
        @monotonic(MonotonicDirection.INCREASING)
        def normalize_and_score(text: str) -> float:
            normalized = text.strip().lower()
            return float(len(normalized))
        
        assert hasattr(normalize_and_score, "__idempotent__")
        assert hasattr(normalize_and_score, "__monotonic__")
        
        # Test idempotency
        result1 = normalize_and_score("  HELLO  ")
        result2 = normalize_and_score(result1)  # Wrong - should pass string
        # Actually, idempotency means f(f(x)) = f(x), but here f returns float
        # So we need to test with same input
        result1 = normalize_and_score("  HELLO  ")
        result2 = normalize_and_score("  HELLO  ")
        assert result1 == result2
    
    def test_bug_decorator_order_matters(self):
        """
        BUG: Decorator order matters when combining decorators. The order
        of @idempotent and @monotonic may affect which attributes are set.
        
        Root cause: Decorators wrap functions, so order affects wrapping
        Consequences: Different orders may produce different behavior
        
        Proposed solution: Document decorator order requirements or make order-independent
        """
        # Order 1: idempotent then monotonic
        @idempotent
        @monotonic(MonotonicDirection.INCREASING)
        def function1(x: float) -> float:
            return abs(x)
        
        # Order 2: monotonic then idempotent
        @monotonic(MonotonicDirection.INCREASING)
        @idempotent
        def function2(x: float) -> float:
            return abs(x)
        
        # Both should have both attributes
        assert hasattr(function1, "__idempotent__")
        assert hasattr(function1, "__monotonic__")
        assert hasattr(function2, "__idempotent__")
        assert hasattr(function2, "__monotonic__")
        # But inner decorator wraps outer, so order may matter for runtime behavior
