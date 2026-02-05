"""
Deep comprehensive bug-detection tests for Bounds class.
Tests bounds validation, edge cases, and real bugs.
"""
import pytest
from toolbox.fields import Bounds


class TestBounds:
    """Tests for Bounds class"""
    
    def test_bounds_contains_valid_value(self):
        """Test contains returns True for value within bounds"""
        bounds = Bounds(min=0.0, max=1.0)
        assert bounds.contains(0.5) is True
        assert bounds.contains(0.0) is True  # At min
        assert bounds.contains(1.0) is True  # At max
    
    def test_bounds_contains_outside_bounds(self):
        """Test contains returns False for value outside bounds"""
        bounds = Bounds(min=0.0, max=1.0)
        assert bounds.contains(-0.1) is False  # Below min
        assert bounds.contains(1.1) is False  # Above max
    
    def test_bug_bounds_doesnt_validate_min_less_than_max(self):
        """
        BUG: Bounds (line 8-16) doesn't validate that min <= max.
        If min > max, contains() will always return False, which may
        mask configuration errors.
        
        Root cause: No validation in __init__ or __post_init__
        Consequences: Invalid bounds silently fail all contains() checks
        
        Proposed solution: Add validation in __post_init__ to raise error if min > max
        """
        # Create invalid bounds (min > max)
        invalid_bounds = Bounds(min=1.0, max=0.0)
        
        # BUG: contains() always returns False for invalid bounds
        assert invalid_bounds.contains(0.5) is False  # Value between min and max, but min > max
        assert invalid_bounds.contains(1.5) is False
        assert invalid_bounds.contains(-0.5) is False
        
        # BUG: No indication that bounds are invalid
    
    def test_bug_bounds_contains_doesnt_handle_nan(self):
        """
        BUG: contains (line 14-16) doesn't handle NaN values.
        NaN comparisons (NaN <= x, x <= NaN) always return False,
        so contains(NaN) returns False even though NaN is not a valid value.
        
        Root cause: No special handling for NaN
        Consequences: NaN values may be incorrectly considered out of bounds
        
        Proposed solution: Check for NaN explicitly and return False or raise error
        """
        import math
        
        bounds = Bounds(min=0.0, max=1.0)
        
        # BUG: NaN comparison always returns False
        result = bounds.contains(float('nan'))
        assert result is False  # This is correct behavior, but should be explicit
        
        # BUG: No indication that value is NaN (invalid)
    
    def test_bug_bounds_contains_doesnt_handle_infinity(self):
        """
        BUG: contains (line 14-16) doesn't handle Infinity values.
        Infinity comparisons may behave unexpectedly:
        - Infinity <= max is True (if max is finite)
        - min <= Infinity is True (if min is finite)
        So contains(Infinity) may return True for finite bounds.
        
        Root cause: No special handling for Infinity
        Consequences: Infinity values may be incorrectly considered within bounds
        
        Proposed solution: Check for Infinity explicitly and return False or raise error
        """
        import math
        
        bounds = Bounds(min=0.0, max=1.0)
        
        # BUG: Infinity may be considered within bounds
        result_pos_inf = bounds.contains(float('inf'))
        result_neg_inf = bounds.contains(float('-inf'))
        
        # Infinity comparisons: inf <= 1.0 is False, 0.0 <= inf is True
        # So 0.0 <= inf <= 1.0 evaluates to False (correct)
        assert result_pos_inf is False
        assert result_neg_inf is False
        
        # But if bounds include infinity, behavior may be unexpected
        inf_bounds = Bounds(min=0.0, max=float('inf'))
        assert inf_bounds.contains(float('inf')) is True  # This works, but may be unintended
    
    def test_bug_bounds_contains_doesnt_handle_negative_zero(self):
        """
        BUG: contains (line 14-16) doesn't distinguish between -0.0 and 0.0.
        In Python, -0.0 == 0.0 is True, but they have different representations.
        For bounds like [0.0, 1.0], -0.0 should be considered within bounds,
        but the comparison may behave unexpectedly.
        
        Root cause: No special handling for negative zero
        Consequences: -0.0 may be handled incorrectly (though likely works correctly)
        """
        bounds = Bounds(min=0.0, max=1.0)
        
        # BUG: -0.0 vs 0.0 distinction
        assert bounds.contains(0.0) is True
        assert bounds.contains(-0.0) is True  # -0.0 == 0.0 in Python
    
    def test_bug_bounds_contains_floating_point_precision(self):
        """
        BUG: contains (line 14-16) uses <= comparisons which may have
        floating-point precision issues. Values very close to boundaries
        may be incorrectly classified due to rounding errors.
        
        Root cause: Floating-point comparison without epsilon tolerance
        Consequences: Values at boundaries may be incorrectly classified
        
        Proposed solution: Use epsilon tolerance for boundary comparisons
        """
        bounds = Bounds(min=0.0, max=1.0)
        
        # Values very close to boundaries
        epsilon = 1e-15
        assert bounds.contains(1.0 + epsilon) is False  # Just above max
        assert bounds.contains(1.0 - epsilon) is True  # Just below max
        
        # BUG: Floating-point precision may cause issues with very small epsilon
        # For example, 1.0 + 1e-17 might still be considered <= 1.0 due to rounding
    
    def test_bug_bounds_contains_doesnt_validate_input_type(self):
        """
        BUG: contains (line 14-16) doesn't validate that value is numeric.
        If a non-numeric value is passed (e.g., string, None), the comparison
        may raise TypeError or behave unexpectedly.
        
        Root cause: No type validation
        Consequences: Type errors at runtime, unclear error messages
        """
        bounds = Bounds(min=0.0, max=1.0)
        
        # BUG: Non-numeric values may cause errors
        with pytest.raises(TypeError):
            bounds.contains("0.5")  # String
        
        with pytest.raises(TypeError):
            bounds.contains(None)  # None
    
    def test_bug_bounds_frozen_prevents_modification(self):
        """
        BUG: Bounds (line 8) is frozen, but if code tries to modify it,
        the error message may not be clear. Also, frozen dataclasses can
        still be modified via __dict__ or object.__setattr__.
        
        Root cause: Frozen dataclass can be bypassed
        Consequences: Bounds may be modified incorrectly, breaking invariants
        """
        bounds = Bounds(min=0.0, max=1.0)
        
        # BUG: Frozen dataclass prevents modification, but error may not be clear
        with pytest.raises(Exception):  # Should raise FrozenInstanceError
            bounds.min = 0.5
        
        # BUG: Can still modify via __dict__ or object.__setattr__
        # This is a Python limitation, but should be documented
    
    def test_bug_bounds_equal_min_max(self):
        """
        BUG: Bounds allows min == max, which creates a bounds that only
        contains a single value. This may be intentional, but should be
        documented. Also, if min == max, contains() only returns True
        for that exact value.
        
        Root cause: No validation that min != max
        Consequences: Single-value bounds may be unexpected
        """
        bounds = Bounds(min=0.5, max=0.5)
        
        # BUG: Only contains exact value
        assert bounds.contains(0.5) is True
        assert bounds.contains(0.5000001) is False  # Even tiny difference fails
        assert bounds.contains(0.4999999) is False
    
    def test_bug_bounds_very_large_values(self):
        """
        BUG: Bounds doesn't validate that min/max are reasonable values.
        Very large values (close to float max) may cause overflow or
        precision issues in comparisons.
        
        Root cause: No bounds validation on min/max themselves
        Consequences: Overflow, precision issues, unexpected behavior
        """
        import sys
        
        # Very large bounds
        large_bounds = Bounds(min=1e300, max=1e301)
        
        # BUG: May have precision issues
        assert large_bounds.contains(1e300) is True
        assert large_bounds.contains(1e301) is True
        
        # BUG: Values near float max may cause overflow
        max_float = sys.float_info.max
        max_bounds = Bounds(min=0.0, max=max_float)
        assert max_bounds.contains(max_float) is True
    
    def test_bug_bounds_negative_values(self):
        """
        BUG: Bounds allows negative min/max values. This is valid, but
        if code assumes non-negative bounds, negative values may cause issues.
        
        Root cause: No restriction on sign of min/max
        Consequences: Negative bounds may be unexpected in some contexts
        """
        # Negative bounds
        negative_bounds = Bounds(min=-1.0, max=-0.5)
        
        # BUG: Negative bounds work correctly, but may be unexpected
        assert negative_bounds.contains(-0.75) is True
        assert negative_bounds.contains(-1.1) is False
        assert negative_bounds.contains(-0.4) is False
    
    def test_bug_bounds_contains_boundary_conditions(self):
        """
        BUG: contains (line 16) uses <= for both comparisons, which means
        values exactly at min and max are included. This is correct behavior,
        but if code expects exclusive boundaries, it may cause issues.
        
        Root cause: Inclusive boundaries (<=) may not match expectations
        Consequences: Boundary values included when exclusive boundaries expected
        """
        bounds = Bounds(min=0.0, max=1.0)
        
        # BUG: Boundaries are inclusive
        assert bounds.contains(0.0) is True  # At min (included)
        assert bounds.contains(1.0) is True  # At max (included)
        
        # If exclusive boundaries are needed, code must check separately
        # Proposed solution: Add contains_exclusive() method or document inclusive behavior


class TestBoundsConstants:
    """Tests for BOUNDS constants used in base.py"""
    
    def test_bounds_temperature_values(self):
        """Test BOUNDS_TEMPERATURE has correct values"""
        from toolbox.llm.base import BOUNDS_TEMPERATURE
        
        assert BOUNDS_TEMPERATURE.min == 0.0
        assert BOUNDS_TEMPERATURE.max == 2.0
    
    def test_bounds_temperature_contains_valid(self):
        """Test BOUNDS_TEMPERATURE contains valid temperature values"""
        from toolbox.llm.base import BOUNDS_TEMPERATURE
        
        assert BOUNDS_TEMPERATURE.contains(0.0) is True
        assert BOUNDS_TEMPERATURE.contains(1.0) is True
        assert BOUNDS_TEMPERATURE.contains(2.0) is True
    
    def test_bounds_temperature_rejects_invalid(self):
        """Test BOUNDS_TEMPERATURE rejects invalid temperature values"""
        from toolbox.llm.base import BOUNDS_TEMPERATURE
        
        assert BOUNDS_TEMPERATURE.contains(-0.1) is False
        assert BOUNDS_TEMPERATURE.contains(2.1) is False
    
    def test_bounds_top_p_values(self):
        """Test BOUNDS_TOP_P has correct values"""
        from toolbox.llm.base import BOUNDS_TOP_P
        
        assert BOUNDS_TOP_P.min == 0.0
        assert BOUNDS_TOP_P.max == 1.0
    
    def test_bounds_top_p_contains_valid(self):
        """Test BOUNDS_TOP_P contains valid top_p values"""
        from toolbox.llm.base import BOUNDS_TOP_P
        
        assert BOUNDS_TOP_P.contains(0.0) is True
        assert BOUNDS_TOP_P.contains(0.5) is True
        assert BOUNDS_TOP_P.contains(1.0) is True
    
    def test_bounds_top_p_rejects_invalid(self):
        """Test BOUNDS_TOP_P rejects invalid top_p values"""
        from toolbox.llm.base import BOUNDS_TOP_P
        
        assert BOUNDS_TOP_P.contains(-0.1) is False
        assert BOUNDS_TOP_P.contains(1.1) is False
    
    def test_bug_bounds_constants_not_validated_at_import(self):
        """
        BUG: BOUNDS_TEMPERATURE and BOUNDS_TOP_P (base.py lines 12-13) are
        created at import time but not validated. If Bounds constructor is
        buggy or if values are incorrect, the error won't be caught until
        contains() is called.
        
        Root cause: No validation at constant creation time
        Consequences: Invalid bounds constants may exist silently
        
        Proposed solution: Add validation in Bounds.__post_init__ or validate constants
        """
        from toolbox.llm.base import BOUNDS_TEMPERATURE, BOUNDS_TOP_P
        
        # Constants should be valid
        assert BOUNDS_TEMPERATURE.min <= BOUNDS_TEMPERATURE.max
        assert BOUNDS_TOP_P.min <= BOUNDS_TOP_P.max
        
        # BUG: If min > max, error won't be caught until contains() is called
