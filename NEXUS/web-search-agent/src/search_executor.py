"""
Nexus Web Search Agent - Search Executor
Execute web searches (SearXNG preferred, DuckDuckGo/Google fallback)
"""

from typing import List, Optional, Dict, Any
from dataclasses import dataclass
import time
import requests
from urllib.parse import quote

# Import SearXNG executor (preferred)
try:
    from .searxng_executor import SearXNGExecutor, SearchResult
    SEARXNG_AVAILABLE = True
except ImportError:
    SEARXNG_AVAILABLE = False
    # Fallback SearchResult definition
    @dataclass
    class SearchResult:
        """Search result"""
        title: str
        url: str
        snippet: str
        rank: int
        source: str  # duckduckgo, google, searxng, etc.


class SearchExecutor:
    """
    Search executor for executing web searches.
    
    Uses SearXNG (privacy-respecting metasearch) by default.
    Falls back to DuckDuckGo/Google if SearXNG unavailable.
    """
    
    def __init__(
        self,
        default_engine: str = "searxng",
        searxng_url: Optional[str] = None,
        google_api_key: Optional[str] = None
    ):
        """
        Initialize search executor.
        
        Args:
            default_engine: Default search engine (searxng, duckduckgo, google)
            searxng_url: SearXNG instance URL (default: public instance)
            google_api_key: Optional Google API key (for fallback)
        """
        self.default_engine = default_engine
        self.google_api_key = google_api_key
        
        # Initialize SearXNG executor if available
        if SEARXNG_AVAILABLE and default_engine == "searxng":
            self.searxng_executor = SearXNGExecutor(
                searxng_url=searxng_url or "https://searx.be"
            )
        else:
            self.searxng_executor = None
    
    def search(
        self,
        query: str,
        max_results: int = 10,
        engine: Optional[str] = None
    ) -> List[SearchResult]:
        """
        Execute web search.
        
        Args:
            query: Search query
            max_results: Maximum number of results
            engine: Search engine (defaults to default_engine)
            
        Returns:
            List of search results
        """
        engine = engine or self.default_engine
        
        # Prefer SearXNG if available
        if engine == "searxng" and self.searxng_executor:
            return self.searxng_executor.search_web(query, max_results)
        elif engine == "duckduckgo":
            return self._search_duckduckgo(query, max_results)
        elif engine == "google":
            return self._search_google(query, max_results)
        else:
            # Fallback: try SearXNG if available, otherwise DuckDuckGo
            if self.searxng_executor:
                return self.searxng_executor.search_web(query, max_results)
            else:
                return self._search_duckduckgo(query, max_results)
    
    def _search_duckduckgo(self, query: str, max_results: int) -> List[SearchResult]:
        """
        Search using DuckDuckGo (HTML scraping).
        
        Args:
            query: Search query
            max_results: Maximum number of results
            
        Returns:
            List of search results
        """
        # DuckDuckGo HTML search endpoint
        url = "https://html.duckduckgo.com/html/"
        params = {
            "q": query
        }
        
        try:
            headers = {
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"
            }
            response = requests.get(url, params=params, headers=headers, timeout=10)
            response.raise_for_status()
            
            # Parse HTML results (simplified - would use BeautifulSoup in production)
            results = self._parse_duckduckgo_html(response.text, max_results)
            return results
            
        except Exception as e:
            # Fallback: return empty results
            print(f"DuckDuckGo search error: {e}")
            return []
    
    def _search_google(self, query: str, max_results: int) -> List[SearchResult]:
        """
        Search using Google Custom Search API.
        
        Args:
            query: Search query
            max_results: Maximum number of results
            
        Returns:
            List of search results
        """
        if not self.google_api_key:
            raise ValueError("Google API key required for Google search")
        
        # Google Custom Search API
        url = "https://www.googleapis.com/customsearch/v1"
        params = {
            "key": self.google_api_key,
            "cx": "YOUR_SEARCH_ENGINE_ID",  # Would be configured
            "q": query,
            "num": min(max_results, 10)  # Google API limit
        }
        
        try:
            response = requests.get(url, params=params, timeout=10)
            response.raise_for_status()
            
            data = response.json()
            results = []
            
            for i, item in enumerate(data.get("items", [])[:max_results]):
                results.append(SearchResult(
                    title=item.get("title", ""),
                    url=item.get("link", ""),
                    snippet=item.get("snippet", ""),
                    rank=i + 1,
                    source="google"
                ))
            
            return results
            
        except Exception as e:
            print(f"Google search error: {e}")
            return []
    
    def _parse_duckduckgo_html(self, html: str, max_results: int) -> List[SearchResult]:
        """
        Parse DuckDuckGo HTML results (simplified).
        
        Args:
            html: HTML content
            max_results: Maximum number of results
            
        Returns:
            List of search results
        """
        # Simplified parsing - would use BeautifulSoup in production
        results = []
        
        # Basic regex/string parsing (production would use proper HTML parser)
        import re
        
        # Find result blocks (simplified pattern)
        result_pattern = r'<a[^>]*class="result__a"[^>]*href="([^"]*)"[^>]*>([^<]*)</a>'
        matches = re.findall(result_pattern, html)
        
        for i, (url, title) in enumerate(matches[:max_results]):
            # Extract snippet (simplified)
            snippet = ""  # Would extract from HTML
            
            results.append(SearchResult(
                title=title.strip(),
                url=url,
                snippet=snippet,
                rank=i + 1,
                source="duckduckgo"
            ))
        
        return results
