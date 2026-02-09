"""
Nexus Web Search Agent - Result Ranker
Rank search results by relevance
"""

from typing import List
from .search_executor import SearchResult


class ResultRanker:
    """
    Result ranker for ranking search results by relevance.
    
    Ranks results based on:
    - Query term matching
    - Source reliability
    - Result snippet quality
    - URL domain reputation
    """
    
    def __init__(self):
        """Initialize result ranker"""
        # Trusted domains (would be configurable)
        self.trusted_domains = {
            "wikipedia.org",
            "github.com",
            "stackoverflow.com",
            "arxiv.org",
            "ieee.org",
            "acm.org"
        }
    
    def rank_results(
        self,
        results: List[SearchResult],
        query: str
    ) -> List[SearchResult]:
        """
        Rank search results by relevance.
        
        Args:
            results: List of search results
            query: Original search query
            
        Returns:
            Ranked list of search results
        """
        # Score each result
        scored_results = []
        for result in results:
            score = self._score_result(result, query)
            scored_results.append((score, result))
        
        # Sort by score (highest first)
        scored_results.sort(key=lambda x: x[0], reverse=True)
        
        # Re-rank results
        ranked_results = []
        for rank, (score, result) in enumerate(scored_results, start=1):
            ranked_results.append(SearchResult(
                title=result.title,
                url=result.url,
                snippet=result.snippet,
                rank=rank,
                source=result.source
            ))
        
        return ranked_results
    
    def _score_result(self, result: SearchResult, query: str) -> float:
        """
        Score a search result.
        
        Args:
            result: Search result
            query: Search query
            
        Returns:
            Score (0.0 to 1.0)
        """
        score = 0.0
        
        # Query term matching in title (0.4 weight)
        title_score = self._match_score(result.title.lower(), query.lower())
        score += 0.4 * title_score
        
        # Query term matching in snippet (0.3 weight)
        snippet_score = self._match_score(result.snippet.lower(), query.lower())
        score += 0.3 * snippet_score
        
        # Domain trust (0.2 weight)
        domain_score = self._domain_score(result.url)
        score += 0.2 * domain_score
        
        # Original rank (0.1 weight) - prefer higher original rank
        rank_score = 1.0 - (result.rank - 1) / max(len([result]), 10.0)
        score += 0.1 * rank_score
        
        return min(score, 1.0)
    
    def _match_score(self, text: str, query: str) -> float:
        """
        Calculate query term matching score.
        
        Args:
            text: Text to search in
            query: Query string
            
        Returns:
            Match score (0.0 to 1.0)
        """
        query_terms = query.split()
        
        if not query_terms:
            return 0.0
        
        # Count how many query terms appear in text
        matches = sum(1 for term in query_terms if term in text)
        
        # Score based on fraction of terms matched
        return matches / len(query_terms)
    
    def _domain_score(self, url: str) -> float:
        """
        Calculate domain trust score.
        
        Args:
            url: URL
            
        Returns:
            Domain score (0.0 to 1.0)
        """
        try:
            from urllib.parse import urlparse
            domain = urlparse(url).netloc.lower()
            
            # Check if domain is trusted
            for trusted in self.trusted_domains:
                if trusted in domain:
                    return 1.0
            
            # Default score for unknown domains
            return 0.5
            
        except Exception:
            return 0.5
