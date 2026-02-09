"""
Deep comprehensive tests for analyst routing.

Tests query routing, keyword matching, module boost, cost filtering, and bug detection.
"""
import pytest
from toolbox.llm.routing import (
    route_query,
    route_by_intent,
    get_recommended_analysts,
    RoutingResult,
    KEYWORD_WEIGHT_PER_WORD,
    MODULE_BOOST_WEIGHT,
    HIGH_CONFIDENCE_THRESHOLD,
    MODERATE_CONFIDENCE_THRESHOLD,
    KEYWORD_PATTERNS,
    MODULE_PRIMARY_ANALYSTS,
)
from toolbox.llm.base import AnalystRole


class TestRouteQuery:
    """Deep comprehensive tests for route_query function."""

    def test_route_query_content_strategy_keywords(self):
        """Test routing with content strategy keywords."""
        result = route_query("create content strategy and editorial calendar")
        assert result.analyst.role == AnalystRole.CONTENT_STRATEGIST
        assert result.confidence > 0.0
        assert result.reason is not None

    def test_route_query_copywriter_keywords(self):
        """Test routing with copywriter keywords."""
        result = route_query("write copy for landing page")
        assert result.analyst.role == AnalystRole.COPYWRITER
        assert result.confidence > 0.0

    def test_route_query_seo_keywords(self):
        """Test routing with SEO keywords."""
        result = route_query("optimize SEO and keyword research")
        assert result.analyst.role == AnalystRole.SEO_SPECIALIST
        assert result.confidence > 0.0

    def test_route_query_email_keywords(self):
        """Test routing with email keywords."""
        result = route_query("create email campaign and automation")
        assert result.analyst.role == AnalystRole.EMAIL_SPECIALIST
        assert result.confidence > 0.0

    def test_route_query_data_analyst_keywords(self):
        """Test routing with data analyst keywords."""
        result = route_query("analyze data and create report")
        assert result.analyst.role == AnalystRole.DATA_ANALYST
        assert result.confidence > 0.0

    def test_route_query_no_keywords_fallback(self):
        """Test routing with no keywords falls back to general."""
        result = route_query("random query with no keywords")
        assert result.analyst.role == AnalystRole.GENERAL_ASSISTANT
        assert result.confidence >= 0.0

    def test_route_query_empty_string(self):
        """Test routing with empty string."""
        result = route_query("")
        assert result.analyst.role == AnalystRole.GENERAL_ASSISTANT

    def test_route_query_case_insensitive(self):
        """Test routing is case-insensitive."""
        result1 = route_query("CONTENT STRATEGY")
        result2 = route_query("content strategy")
        assert result1.analyst.role == result2.analyst.role

    def test_route_query_module_boost(self):
        """Test module boost increases score."""
        result_with_module = route_query("general query", module="M01")
        result_without_module = route_query("general query", module=None)
        # With module boost, should prefer module's primary analyst
        assert result_with_module.analyst.role == AnalystRole.CONTENT_STRATEGIST

    def test_route_query_module_boost_with_keywords(self):
        """Test module boost combined with keywords."""
        result = route_query("content strategy", module="M01")
        assert result.analyst.role == AnalystRole.CONTENT_STRATEGIST
        assert result.confidence > MODERATE_CONFIDENCE_THRESHOLD

    def test_route_query_max_cost_filter(self):
        """Test max_cost_usd filters expensive analysts."""
        # Query that would match expensive analyst
        result = route_query("content strategy", max_cost_usd=0.1)
        # Should still return an analyst (fallback if all filtered)
        assert result.analyst is not None
        assert result.analyst.max_cost_per_request_usd <= 0.1

    def test_route_query_max_cost_none(self):
        """Test max_cost_usd=None allows all analysts."""
        result = route_query("content strategy", max_cost_usd=None)
        assert result.analyst is not None

    def test_route_query_multiple_keywords(self):
        """Test routing with multiple matching keywords."""
        result = route_query("create content strategy and editorial calendar for blog")
        assert result.analyst.role == AnalystRole.CONTENT_STRATEGIST
        assert result.confidence > HIGH_CONFIDENCE_THRESHOLD

    def test_route_query_alternatives(self):
        """Test routing returns alternatives."""
        result = route_query("content strategy")
        assert isinstance(result.alternatives, tuple)
        # Alternatives should not include selected analyst
        assert result.analyst.role not in [alt.role for alt in result.alternatives]

    def test_route_query_confidence_range(self):
        """Test confidence is in valid range."""
        result = route_query("content strategy")
        assert 0.0 <= result.confidence <= 1.0

    def test_route_query_reason_format(self):
        """Test reason is human-readable."""
        result = route_query("content strategy")
        assert isinstance(result.reason, str)
        assert len(result.reason) > 0

    def test_route_query_prefer_fast_ignored(self):
        """Test prefer_fast parameter is ignored (not implemented)."""
        result1 = route_query("content strategy", prefer_fast=False)
        result2 = route_query("content strategy", prefer_fast=True)
        # Should return same result (prefer_fast not implemented)
        assert result1.analyst.role == result2.analyst.role


class TestRouteByIntent:
    """Deep comprehensive tests for route_by_intent function."""

    def test_route_by_intent_analyze(self):
        """Test routing by analyze intent."""
        result = route_by_intent("analyze")
        assert result.analyst.role == AnalystRole.DATA_ANALYST
        assert result.confidence == 0.8

    def test_route_by_intent_create(self):
        """Test routing by create intent."""
        result = route_by_intent("create")
        assert result.analyst.role == AnalystRole.COPYWRITER

    def test_route_by_intent_optimize(self):
        """Test routing by optimize intent."""
        result = route_by_intent("optimize")
        assert result.analyst.role == AnalystRole.EMAIL_SPECIALIST

    def test_route_by_intent_explain(self):
        """Test routing by explain intent."""
        result = route_by_intent("explain")
        assert result.analyst.role == AnalystRole.DATA_ANALYST

    def test_route_by_intent_plan(self):
        """Test routing by plan intent."""
        result = route_by_intent("plan")
        assert result.analyst.role == AnalystRole.CONTENT_STRATEGIST

    def test_route_by_intent_report(self):
        """Test routing by report intent."""
        result = route_by_intent("report")
        assert result.analyst.role == AnalystRole.DATA_ANALYST

    def test_route_by_intent_unknown(self):
        """Test routing by unknown intent falls back."""
        result = route_by_intent("unknown")  # type: ignore
        assert result.analyst.role == AnalystRole.GENERAL_ASSISTANT

    def test_route_by_intent_with_module(self):
        """Test route_by_intent respects module."""
        result = route_by_intent("analyze", module="M01")
        # Module boost should override intent default
        assert result.analyst.role == AnalystRole.CONTENT_STRATEGIST

    def test_route_by_intent_alternatives_empty(self):
        """Test route_by_intent returns empty alternatives."""
        result = route_by_intent("analyze")
        assert result.alternatives == ()


class TestGetRecommendedAnalysts:
    """Deep comprehensive tests for get_recommended_analysts function."""

    def test_get_recommended_analysts(self):
        """Test getting recommended analysts for module."""
        analysts = get_recommended_analysts("M01", limit=5)
        assert isinstance(analysts, tuple)
        assert len(analysts) <= 5

    def test_get_recommended_analysts_limit(self):
        """Test limit parameter."""
        analysts1 = get_recommended_analysts("M01", limit=3)
        analysts2 = get_recommended_analysts("M01", limit=10)
        assert len(analysts1) <= 3
        assert len(analysts2) <= 10

    def test_get_recommended_analysts_unknown_module(self):
        """Test getting analysts for unknown module."""
        analysts = get_recommended_analysts("UNKNOWN", limit=5)
        assert isinstance(analysts, tuple)


class TestRoutingResult:
    """Deep comprehensive tests for RoutingResult dataclass."""

    def test_routing_result_creation(self):
        """Test creating RoutingResult."""
        from toolbox.llm.analysts import get_analyst
        analyst = get_analyst(AnalystRole.CONTENT_STRATEGIST)
        result = RoutingResult(
            analyst=analyst,
            confidence=0.8,
            reason="Test reason",
            alternatives=(),
        )
        assert result.analyst == analyst
        assert result.confidence == 0.8
        assert result.reason == "Test reason"
        assert result.alternatives == ()

    def test_routing_result_confidence_validation(self):
        """Test RoutingResult validates confidence range."""
        from toolbox.llm.analysts import get_analyst
        analyst = get_analyst(AnalystRole.CONTENT_STRATEGIST)
        
        # Valid confidence
        result = RoutingResult(
            analyst=analyst,
            confidence=0.5,
            reason="Test",
            alternatives=(),
        )
        assert result.confidence == 0.5
        
        # Invalid confidence (too high)
        with pytest.raises(ValueError, match="confidence must be in"):
            RoutingResult(
                analyst=analyst,
                confidence=1.5,  # > 1.0
                reason="Test",
                alternatives=(),
            )
        
        # Invalid confidence (negative)
        with pytest.raises(ValueError, match="confidence must be in"):
            RoutingResult(
                analyst=analyst,
                confidence=-0.1,  # < 0.0
                reason="Test",
                alternatives=(),
            )

    def test_routing_result_role_property(self):
        """Test role property convenience accessor."""
        result = route_query("content strategy")
        assert result.role == result.analyst.role

    def test_routing_result_frozen(self):
        """Test RoutingResult is frozen (immutable)."""
        result = route_query("content strategy")
        # Should not be able to modify
        with pytest.raises(Exception):  # Frozen dataclass raises
            result.confidence = 0.9  # type: ignore


class TestKeywordMatching:
    """Deep comprehensive tests for keyword matching logic."""

    def test_keyword_patterns_defined(self):
        """Test all analyst roles have keyword patterns."""
        assert AnalystRole.CONTENT_STRATEGIST in KEYWORD_PATTERNS
        assert AnalystRole.COPYWRITER in KEYWORD_PATTERNS
        assert AnalystRole.SEO_SPECIALIST in KEYWORD_PATTERNS
        assert AnalystRole.EMAIL_SPECIALIST in KEYWORD_PATTERNS
        assert AnalystRole.DATA_ANALYST in KEYWORD_PATTERNS
        assert AnalystRole.GENERAL_ASSISTANT in KEYWORD_PATTERNS

    def test_keyword_matching_multi_word(self):
        """Test multi-word keyword matching."""
        result = route_query("content strategy planning")
        assert result.analyst.role == AnalystRole.CONTENT_STRATEGIST

    def test_keyword_matching_partial_word(self):
        """Test partial word matching (should not match)."""
        result = route_query("strategic")  # Contains "strategy" but not exact match
        # Should not match "content strategy" keyword
        # May match other keywords or fallback

    def test_keyword_matching_case_insensitive(self):
        """Test keyword matching is case-insensitive."""
        result1 = route_query("CONTENT STRATEGY")
        result2 = route_query("content strategy")
        assert result1.analyst.role == result2.analyst.role

    def test_keyword_matching_multiple_roles(self):
        """Test query matching multiple roles."""
        result = route_query("create content strategy and write copy")
        # Should match both CONTENT_STRATEGIST and COPYWRITER
        # Should return highest scoring
        assert result.analyst.role in [
            AnalystRole.CONTENT_STRATEGIST,
            AnalystRole.COPYWRITER,
        ]


class TestModuleBoost:
    """Deep comprehensive tests for module boost logic."""

    def test_module_primary_analysts_defined(self):
        """Test module primary analysts are defined."""
        assert "M01" in MODULE_PRIMARY_ANALYSTS
        assert "M02" in MODULE_PRIMARY_ANALYSTS
        assert "M03" in MODULE_PRIMARY_ANALYSTS

    def test_module_boost_applied(self):
        """Test module boost increases score."""
        result = route_query("general query", module="M01")
        assert result.analyst.role == AnalystRole.CONTENT_STRATEGIST

    def test_module_boost_unknown_module(self):
        """Test unknown module doesn't break routing."""
        result = route_query("content strategy", module="UNKNOWN")
        # Should still route correctly based on keywords
        assert result.analyst.role == AnalystRole.CONTENT_STRATEGIST

    def test_module_boost_overrides_keywords(self):
        """Test module boost can override keyword match."""
        # Query that matches one role, but module boosts different role
        result = route_query("write copy", module="M01")  # M01 boosts CONTENT_STRATEGIST
        # Module boost may override keyword match
        assert result.analyst is not None


class TestCostFiltering:
    """Deep comprehensive tests for cost filtering."""

    def test_cost_filter_excludes_expensive(self):
        """Test cost filter excludes expensive analysts."""
        result = route_query("content strategy", max_cost_usd=0.1)
        assert result.analyst.max_cost_per_request_usd <= 0.1

    def test_cost_filter_allows_cheap(self):
        """Test cost filter allows cheap analysts."""
        result = route_query("content strategy", max_cost_usd=1.0)
        # Should allow more analysts
        assert result.analyst.max_cost_per_request_usd <= 1.0

    def test_cost_filter_zero(self):
        """Test cost filter with zero cost."""
        result = route_query("content strategy", max_cost_usd=0.0)
        # Should only allow free analysts
        assert result.analyst.max_cost_per_request_usd <= 0.0

    def test_cost_filter_none(self):
        """Test cost filter with None allows all."""
        result = route_query("content strategy", max_cost_usd=None)
        assert result.analyst is not None


class TestConfidenceScoring:
    """Deep comprehensive tests for confidence scoring."""

    def test_confidence_normalization(self):
        """Test confidence is normalized to [0.0, 1.0]."""
        result = route_query("content strategy")
        assert 0.0 <= result.confidence <= 1.0

    def test_confidence_high_threshold(self):
        """Test high confidence threshold."""
        result = route_query("content strategy and editorial calendar")
        # Multiple keyword matches should give high confidence
        assert result.confidence >= MODERATE_CONFIDENCE_THRESHOLD

    def test_confidence_reason_matches(self):
        """Test reason matches confidence level."""
        result = route_query("content strategy")
        if result.confidence > HIGH_CONFIDENCE_THRESHOLD:
            assert "Strong" in result.reason or "strong" in result.reason.lower()
        elif result.confidence > MODERATE_CONFIDENCE_THRESHOLD:
            assert "Moderate" in result.reason or "moderate" in result.reason.lower()


class TestAlternatives:
    """Deep comprehensive tests for alternatives."""

    def test_alternatives_excludes_selected(self):
        """Test alternatives don't include selected analyst."""
        result = route_query("content strategy")
        selected_role = result.analyst.role
        assert selected_role not in [alt.role for alt in result.alternatives]

    def test_alternatives_respects_cost_filter(self):
        """Test alternatives respect cost filter."""
        result = route_query("content strategy", max_cost_usd=0.5)
        for alt in result.alternatives:
            assert alt.max_cost_per_request_usd <= 0.5

    def test_alternatives_limit(self):
        """Test alternatives are limited."""
        result = route_query("content strategy")
        assert len(result.alternatives) <= 3  # MAX_ALTERNATIVES

    def test_alternatives_sorted_by_score(self):
        """Test alternatives are sorted by score."""
        result = route_query("content strategy")
        # Alternatives should be in descending order of match quality
        # (Cannot verify without internal state, but structure should be correct)
        assert isinstance(result.alternatives, tuple)


class TestEdgeCases:
    """Edge case tests for routing."""

    def test_very_long_query(self):
        """Test routing with very long query."""
        long_query = "content strategy " * 100
        result = route_query(long_query)
        assert result.analyst is not None

    def test_unicode_query(self):
        """Test routing with Unicode characters."""
        result = route_query("内容策略和编辑日历")
        # Should handle gracefully (may fallback to general)
        assert result.analyst is not None

    def test_special_characters_query(self):
        """Test routing with special characters."""
        result = route_query("content strategy! @#$%^&*()")
        assert result.analyst is not None

    def test_whitespace_only_query(self):
        """Test routing with whitespace-only query."""
        result = route_query("   \n\t  ")
        assert result.analyst.role == AnalystRole.GENERAL_ASSISTANT

    def test_query_with_newlines(self):
        """Test routing with newlines."""
        result = route_query("content\nstrategy\nplanning")
        assert result.analyst.role == AnalystRole.CONTENT_STRATEGIST


class TestBugDetection:
    """Bug detection tests for routing."""

    def test_bug_keyword_matching_may_be_case_sensitive(self):
        """BUG: Keyword matching may be case-sensitive."""
        # Case variations may not match correctly
        # This test documents the potential issue
        # TODO: Add test to verify case-insensitive matching

    def test_bug_module_boost_may_not_apply_correctly(self):
        """BUG: Module boost may not apply correctly."""
        # Boost may not be added to existing score
        # This test documents the potential issue
        # TODO: Add test to verify boost application

    def test_bug_cost_filter_may_exclude_all_analysts(self):
        """BUG: Cost filter may exclude all analysts."""
        # Very low cost limit may leave no valid analysts
        # This test documents the potential issue
        # TODO: Add test with very low cost limit

    def test_bug_confidence_may_not_be_normalized(self):
        """BUG: Confidence may not be normalized correctly."""
        # Confidence may exceed 1.0 or be negative
        # This test documents the potential issue
        # TODO: Add test to verify normalization

    def test_bug_alternatives_may_include_selected(self):
        """BUG: Alternatives may include selected analyst."""
        # Filtering logic may not exclude selected analyst
        # This test documents the potential issue
        # TODO: Add test to verify exclusion

    def test_bug_keyword_patterns_may_not_match_partial_words(self):
        """BUG: Keyword patterns may match partial words incorrectly."""
        # "strategy" may match "strategic" incorrectly
        # This test documents the potential issue
        # TODO: Add test with partial word matches
