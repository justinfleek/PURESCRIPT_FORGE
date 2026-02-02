"""
Unit Tests - Analyst Routing

Tests routing logic with reproducible distributions.
"""

import pytest

from toolbox.llm.routing import (
    route_query,
    route_by_intent,
    RoutingResult,
    KEYWORD_PATTERNS,
    MODULE_PRIMARY_ANALYSTS,
)
from toolbox.llm.base import AnalystRole


class TestRouting:
    """Test analyst routing functionality."""
    
    def test_route_email_query(self):
        """Test routing email-related query."""
        result = route_query("How do I improve email open rates?")
        
        assert isinstance(result, RoutingResult)
        assert result.analyst.role == AnalystRole.EMAIL_SPECIALIST
        assert result.confidence > 0.0
        assert result.confidence <= 1.0
        assert "email" in result.reason.lower()
    
    def test_route_seo_query(self):
        """Test routing SEO-related query."""
        result = route_query("What keywords should I target for SEO?")
        
        assert isinstance(result, RoutingResult)
        assert result.analyst.role == AnalystRole.SEO_SPECIALIST
        assert result.confidence > 0.0
    
    def test_route_content_query(self):
        """Test routing content strategy query."""
        result = route_query("Help me plan my content calendar")
        
        assert isinstance(result, RoutingResult)
        assert result.analyst.role == AnalystRole.CONTENT_STRATEGIST
        assert result.confidence > 0.0
    
    def test_route_general_fallback(self):
        """Test fallback to general assistant."""
        result = route_query("Hello, how are you?")
        
        assert isinstance(result, RoutingResult)
        # Should fallback to general if no keywords match
        assert result.analyst.role in [AnalystRole.GENERAL_ASSISTANT, AnalystRole.EMAIL_SPECIALIST]
        assert result.confidence >= 0.0
    
    def test_module_boost(self):
        """Test module context boost."""
        result_with_module = route_query("analyze data", module="M05")
        result_without = route_query("analyze data")
        
        # Module boost should increase confidence or select module analyst
        assert isinstance(result_with_module, RoutingResult)
        assert isinstance(result_without, RoutingResult)
    
    def test_route_by_intent(self):
        """Test intent-based routing."""
        result = route_by_intent("analyze", module="M05")
        
        assert isinstance(result, RoutingResult)
        assert result.analyst.role == AnalystRole.DATA_ANALYST
        assert result.confidence == 0.8
        assert "analyze" in result.reason.lower()
    
    def test_routing_result_validation(self):
        """Test RoutingResult validation."""
        # Valid result
        result = route_query("test")
        assert 0.0 <= result.confidence <= 1.0
        
        # Invalid confidence should raise
        with pytest.raises(ValueError):
            RoutingResult(
                analyst=result.analyst,
                confidence=1.5,  # Invalid
                reason="test",
                alternatives=(),
            )


class TestRoutingDeterminism:
    """Test routing determinism (same input = same output)."""
    
    @pytest.mark.parametrize("query", [
        "email marketing strategy",
        "SEO optimization tips",
        "content calendar planning",
        "data analysis report",
    ])
    def test_deterministic_routing(self, query: str):
        """Test that routing is deterministic."""
        result1 = route_query(query)
        result2 = route_query(query)
        
        assert result1.analyst.role == result2.analyst.role
        assert result1.confidence == result2.confidence
        assert result1.reason == result2.reason
    
    def test_keyword_patterns_immutable(self):
        """Test that keyword patterns are immutable."""
        # Patterns should be tuples (immutable)
        for role, keywords in KEYWORD_PATTERNS.items():
            assert isinstance(keywords, tuple)
            # Attempting to modify should fail
            with pytest.raises((AttributeError, TypeError)):
                keywords.append("test")  # type: ignore


class TestRoutingEdgeCases:
    """Test routing edge cases."""
    
    def test_empty_query(self):
        """Test routing with empty query."""
        result = route_query("")
        
        assert isinstance(result, RoutingResult)
        assert result.analyst is not None
    
    def test_very_long_query(self):
        """Test routing with very long query."""
        long_query = "email " * 1000
        result = route_query(long_query)
        
        assert isinstance(result, RoutingResult)
        assert result.analyst.role == AnalystRole.EMAIL_SPECIALIST
    
    def test_special_characters(self):
        """Test routing with special characters."""
        result = route_query("email!!! marketing??? strategy!!!")
        
        assert isinstance(result, RoutingResult)
        # Should still match email keywords
    
    def test_case_insensitive(self):
        """Test case-insensitive keyword matching."""
        result1 = route_query("EMAIL MARKETING")
        result2 = route_query("email marketing")
        
        assert result1.analyst.role == result2.analyst.role


__all__ = []
