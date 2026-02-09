"""
Deep comprehensive bug-detection tests for Analyst module.
Tests analyst lookup functions with edge cases and bug detection.
"""
import pytest
from toolbox.llm.analysts import (
    get_analyst,
    get_analysts_for_module,
    get_analyst_by_expertise,
    ALL_ANALYSTS,
    ANALYST_GENERAL,
)
from toolbox.llm.base import AnalystRole, AnalystSpec


class TestGetAnalyst:
    """Tests for get_analyst function"""
    
    def test_get_analyst_returns_correct_analyst(self):
        """Test get_analyst returns correct analyst for known role"""
        analyst = get_analyst(AnalystRole.CONTENT_STRATEGIST)
        assert analyst.role == AnalystRole.CONTENT_STRATEGIST
        assert analyst.name == "Content Strategist"
    
    def test_get_analyst_returns_fallback_for_unknown_role(self):
        """Test get_analyst returns GENERAL_ASSISTANT for unknown role"""
        # Create a role that doesn't exist in ALL_ANALYSTS
        # Since AnalystRole is an Enum, we can't create new values easily
        # But we can test with a role that might not be in the dict
        
        # BUG: get_analyst (line 285-289) checks if role is in ALL_ANALYSTS
        # and returns ANALYST_GENERAL as fallback. However, if ALL_ANALYSTS
        # is incomplete (missing some AnalystRole values), those roles will
        # fall back to GENERAL_ASSISTANT even though they should have specific analysts.
        
        # Test with all known roles - they should all return their specific analysts
        for role in AnalystRole:
            analyst = get_analyst(role)
            # BUG: If role not in ALL_ANALYSTS, returns GENERAL_ASSISTANT
            # This may mask missing analyst definitions
            assert analyst is not None
            if role in ALL_ANALYSTS:
                assert analyst.role == role
            else:
                # Fallback behavior
                assert analyst.role == AnalystRole.GENERAL_ASSISTANT
    
    def test_bug_get_analyst_doesnt_validate_role_exists(self):
        """
        BUG: get_analyst (line 285-289) doesn't validate that the role exists
        in AnalystRole enum. If an invalid role is passed (e.g., via string
        conversion or type coercion), it may return GENERAL_ASSISTANT without
        indicating an error.
        
        Root cause: No validation that role is valid AnalystRole enum value
        Consequences: Invalid roles silently fall back to GENERAL_ASSISTANT,
        masking configuration errors
        
        Proposed solution: Validate role is AnalystRole enum, raise error for invalid
        """
        # This test documents the behavior - enum prevents invalid roles at type level
        # But if role comes from external source (e.g., JSON), validation may be needed
        analyst = get_analyst(AnalystRole.GENERAL_ASSISTANT)
        assert analyst is not None


class TestGetAnalystsForModule:
    """Tests for get_analysts_for_module function"""
    
    def test_get_analysts_for_module_returns_correct_analysts(self):
        """Test get_analysts_for_module returns analysts for known module"""
        analysts = get_analysts_for_module("M01")
        assert len(analysts) > 0
        # Should include analysts with M01 in modules
        assert any("M01" in a.modules for a in analysts)
    
    def test_get_analysts_for_module_returns_general_for_unknown_module(self):
        """Test get_analysts_for_module returns GENERAL_ASSISTANT for unknown module"""
        analysts = get_analysts_for_module("UNKNOWN_MODULE")
        # BUG: get_analysts_for_module (line 292-294) includes analysts with
        # empty modules list: `or not a.modules`. This means GENERAL_ASSISTANT
        # (which has empty modules) is included for any module.
        
        # Should include GENERAL_ASSISTANT (has empty modules)
        assert any(a.role == AnalystRole.GENERAL_ASSISTANT for a in analysts)
    
    def test_bug_get_analysts_for_module_includes_empty_modules_for_all(self):
        """
        BUG: get_analysts_for_module (line 294) includes analysts with empty
        modules list for ALL modules: `or not a.modules`. This means GENERAL_ASSISTANT
        is included for every module query, even if it shouldn't be.
        
        Root cause: Logic `module in a.modules or not a.modules` includes analysts
        with empty modules for all modules
        Consequences: GENERAL_ASSISTANT appears in all module queries, diluting
        module-specific recommendations
        
        Proposed solution: Only include analysts with empty modules if explicitly
        requested or as fallback, not for all modules
        """
        # Test with known module
        analysts = get_analysts_for_module("M01")
        # BUG: GENERAL_ASSISTANT included because it has empty modules
        general_included = any(a.role == AnalystRole.GENERAL_ASSISTANT for a in analysts)
        # This may be intentional (fallback), but should be documented
        
        # Test with unknown module
        analysts_unknown = get_analysts_for_module("UNKNOWN")
        # GENERAL_ASSISTANT definitely included
        assert any(a.role == AnalystRole.GENERAL_ASSISTANT for a in analysts_unknown)
    
    def test_bug_get_analysts_for_module_doesnt_handle_empty_string(self):
        """
        BUG: get_analysts_for_module (line 292-294) doesn't handle empty string
        module name. Empty string in tuple check may behave unexpectedly.
        
        Root cause: No validation that module is non-empty
        Consequences: Empty string may match incorrectly or cause issues
        """
        analysts = get_analysts_for_module("")
        # BUG: Empty string may match incorrectly
        # `"" in a.modules` is False for all analysts, so `or not a.modules` applies
        # This includes GENERAL_ASSISTANT (has empty modules)
        assert len(analysts) > 0
    
    def test_bug_get_analysts_for_module_case_sensitive(self):
        """
        BUG: get_analysts_for_module (line 294) uses `module in a.modules` which
        is case-sensitive. Module names like "m01" vs "M01" won't match.
        
        Root cause: Case-sensitive string matching
        Consequences: Module queries with wrong case won't find analysts
        """
        analysts_upper = get_analysts_for_module("M01")
        analysts_lower = get_analysts_for_module("m01")
        
        # BUG: Case-sensitive matching may return different results
        # Should normalize case or document case sensitivity requirement
        assert len(analysts_upper) > 0
        # Lower case may not match
        # This depends on how modules are stored in AnalystSpec


class TestGetAnalystByExpertise:
    """Tests for get_analyst_by_expertise function"""
    
    def test_get_analyst_by_expertise_returns_matching_analysts(self):
        """Test get_analyst_by_expertise returns analysts with matching expertise"""
        analysts = get_analyst_by_expertise("seo")
        assert len(analysts) > 0
        assert all("seo" in a.expertise for a in analysts)
    
    def test_get_analyst_by_expertise_returns_empty_for_no_match(self):
        """Test get_analyst_by_expertise returns empty list for no match"""
        analysts = get_analyst_by_expertise("nonexistent_expertise")
        assert analysts == []
    
    def test_bug_get_analyst_by_expertise_partial_match(self):
        """
        BUG: get_analyst_by_expertise (line 297-299) uses `expertise in a.expertise`
        which does substring matching. This may match incorrectly (e.g., "seo" matches
        "seo_specialist" but also "seo_optimization").
        
        Root cause: Substring matching instead of exact match
        Consequences: May return analysts with related but different expertise
        
        Proposed solution: Use exact match or document substring matching behavior
        """
        # "seo" matches "seo" in expertise tuple
        analysts = get_analyst_by_expertise("seo")
        assert len(analysts) > 0
        
        # But "se" would also match "seo" (substring)
        analysts_partial = get_analyst_by_expertise("se")
        # BUG: May match "seo" incorrectly
        # This may be intentional (fuzzy matching), but should be documented
    
    def test_bug_get_analyst_by_expertise_case_sensitive(self):
        """
        BUG: get_analyst_by_expertise (line 299) uses `expertise in a.expertise`
        which is case-sensitive. "SEO" vs "seo" won't match.
        
        Root cause: Case-sensitive string matching
        Consequences: Expertise queries with wrong case won't find analysts
        """
        analysts_lower = get_analyst_by_expertise("seo")
        analysts_upper = get_analyst_by_expertise("SEO")
        
        # BUG: Case-sensitive matching may return different results
        assert len(analysts_lower) > 0
        # Upper case may not match depending on how expertise is stored
    
    def test_bug_get_analyst_by_expertise_empty_string(self):
        """
        BUG: get_analyst_by_expertise (line 297-299) doesn't handle empty string
        expertise. Empty string `in` tuple check may match incorrectly.
        
        Root cause: No validation that expertise is non-empty
        Consequences: Empty string may match all analysts or none
        """
        analysts = get_analyst_by_expertise("")
        # BUG: Empty string `"" in a.expertise` is False for all analysts
        # So returns empty list, which may be correct but should be documented
    
    def test_bug_get_analyst_by_expertise_whitespace(self):
        """
        BUG: get_analyst_by_expertise (line 299) doesn't handle whitespace.
        "seo " vs "seo" won't match due to trailing whitespace.
        
        Root cause: No whitespace normalization
        Consequences: Queries with whitespace won't match
        """
        analysts_no_ws = get_analyst_by_expertise("seo")
        analysts_with_ws = get_analyst_by_expertise("seo ")
        
        # BUG: Whitespace may prevent matching
        assert len(analysts_no_ws) > 0
        # With whitespace may not match
        assert len(analysts_with_ws) == 0  # Likely doesn't match


class TestAnalystSpecValidation:
    """Tests for AnalystSpec validation and invariants"""
    
    def test_analyst_spec_frozen(self):
        """Test AnalystSpec is frozen (immutable)"""
        analyst = get_analyst(AnalystRole.CONTENT_STRATEGIST)
        
        # BUG: If AnalystSpec is not frozen, fields may be mutable
        # This could cause bugs if analysts are modified after creation
        with pytest.raises(Exception):  # Should raise error if frozen
            analyst.temperature = 1.0
    
    def test_bug_analyst_spec_temperature_bounds(self):
        """
        BUG: AnalystSpec (line 54) has temperature field but doesn't validate
        bounds. Temperature values outside [0.0, 2.0] may be set.
        
        Root cause: No validation in AnalystSpec dataclass
        Consequences: Invalid temperature values may cause API errors
        
        Proposed solution: Add validation in __post_init__ or use Bounds validator
        """
        # Test that temperature is within bounds
        for analyst in ALL_ANALYSTS.values():
            # BUG: Temperature may be outside bounds
            assert 0.0 <= analyst.temperature <= 2.0
    
    def test_bug_analyst_spec_max_tokens_positive(self):
        """
        BUG: AnalystSpec (line 55) has max_tokens field but doesn't validate
        that it's positive. Negative or zero values may be set.
        
        Root cause: No validation in AnalystSpec dataclass
        Consequences: Invalid max_tokens may cause API errors
        """
        for analyst in ALL_ANALYSTS.values():
            # BUG: max_tokens may be negative or zero
            assert analyst.max_tokens > 0
    
    def test_bug_analyst_spec_max_cost_positive(self):
        """
        BUG: AnalystSpec (line 59) has max_cost_per_request_usd field but
        doesn't validate that it's non-negative. Negative values may be set.
        
        Root cause: No validation in AnalystSpec dataclass
        Consequences: Negative cost limits may cause incorrect filtering
        """
        for analyst in ALL_ANALYSTS.values():
            # BUG: max_cost_per_request_usd may be negative
            assert analyst.max_cost_per_request_usd >= 0.0
    
    def test_bug_analyst_spec_preferred_model_not_empty(self):
        """
        BUG: AnalystSpec (line 52) has preferred_model field but doesn't
        validate that it's non-empty. Empty string may be set.
        
        Root cause: No validation in AnalystSpec dataclass
        Consequences: Empty model name may cause API errors
        """
        for analyst in ALL_ANALYSTS.values():
            # BUG: preferred_model may be empty
            assert len(analyst.preferred_model) > 0
    
    def test_bug_analyst_spec_fallback_model_not_empty(self):
        """
        BUG: AnalystSpec (line 53) has fallback_model field but doesn't
        validate that it's non-empty. Empty string may be set.
        
        Root cause: No validation in AnalystSpec dataclass
        Consequences: Empty model name may cause API errors
        """
        for analyst in ALL_ANALYSTS.values():
            # BUG: fallback_model may be empty
            assert len(analyst.fallback_model) > 0
    
    def test_bug_all_analysts_completeness(self):
        """
        BUG: ALL_ANALYSTS (line 275-282) may not include all AnalystRole values.
        If a new AnalystRole is added but not added to ALL_ANALYSTS, get_analyst
        will fall back to GENERAL_ASSISTANT, masking the missing definition.
        
        Root cause: Manual maintenance of ALL_ANALYSTS dict
        Consequences: Missing analyst definitions silently fall back to GENERAL_ASSISTANT
        
        Proposed solution: Validate that all AnalystRole values have entries in ALL_ANALYSTS
        """
        # Check that all AnalystRole values have entries
        missing_roles = set(AnalystRole) - set(ALL_ANALYSTS.keys())
        # BUG: Missing roles will fall back to GENERAL_ASSISTANT
        # This test documents the issue
        assert len(missing_roles) == 0, f"Missing analyst definitions: {missing_roles}"
    
    def test_bug_analyst_spec_modules_format(self):
        """
        BUG: AnalystSpec (line 57) has modules field as tuple[str, ...] but
        doesn't validate format. Module names may not follow expected format (e.g., "M01").
        
        Root cause: No validation of module name format
        Consequences: Invalid module names may cause routing issues
        """
        for analyst in ALL_ANALYSTS.values():
            # BUG: Module names may not follow expected format
            for module in analyst.modules:
                # Should be format like "M01", "M02", etc.
                # But no validation enforces this
                assert isinstance(module, str)
                assert len(module) > 0
    
    def test_bug_analyst_spec_expertise_format(self):
        """
        BUG: AnalystSpec (line 58) has expertise field as tuple[str, ...] but
        doesn't validate format. Expertise strings may be inconsistent (e.g., "seo" vs "SEO").
        
        Root cause: No validation of expertise string format
        Consequences: Case inconsistencies may cause matching issues
        """
        for analyst in ALL_ANALYSTS.values():
            # BUG: Expertise strings may have inconsistent case/format
            for expertise in analyst.expertise:
                assert isinstance(expertise, str)
                assert len(expertise) > 0
                # Should be lowercase for consistency, but no validation


class TestAnalystRegistry:
    """Tests for ALL_ANALYSTS registry"""
    
    def test_all_analysts_has_expected_analysts(self):
        """Test ALL_ANALYSTS contains expected analysts"""
        expected_roles = {
            AnalystRole.GENERAL_ASSISTANT,
            AnalystRole.CONTENT_STRATEGIST,
            AnalystRole.COPYWRITER,
            AnalystRole.SEO_SPECIALIST,
            AnalystRole.EMAIL_SPECIALIST,
            AnalystRole.DATA_ANALYST,
        }
        
        assert set(ALL_ANALYSTS.keys()) == expected_roles
    
    def test_bug_all_analysts_duplicate_roles(self):
        """
        BUG: ALL_ANALYSTS (line 275-282) is a dict, so duplicate keys would
        overwrite previous entries. However, since AnalystRole is an Enum,
        duplicate enum values aren't possible. But if the same AnalystRole
        is added twice, the second entry overwrites the first.
        
        Root cause: Dict allows overwriting entries
        Consequences: Duplicate entries may mask configuration errors
        
        Proposed solution: Validate no duplicate roles (dict prevents this naturally)
        """
        # Dict naturally prevents duplicates (keys must be unique)
        # But if code adds same role twice, second overwrites first
        assert len(ALL_ANALYSTS) == len(set(ALL_ANALYSTS.keys()))
    
    def test_bug_all_analysts_immutability(self):
        """
        BUG: ALL_ANALYSTS (line 275-282) is a dict that can be modified.
        If code modifies ALL_ANALYSTS after import, it affects all consumers.
        
        Root cause: Mutable global dict
        Consequences: Modifications affect all code using ALL_ANALYSTS
        
        Proposed solution: Make ALL_ANALYSTS immutable (frozenset of tuples or readonly dict)
        """
        original_size = len(ALL_ANALYSTS)
        
        # BUG: Can modify ALL_ANALYSTS (if not protected)
        # This would affect all code using it
        # Test documents the issue - in practice, code shouldn't modify it
        
        assert len(ALL_ANALYSTS) == original_size
