"""
Nexus Web Search Agent - SearXNG Executor
Execute web searches via SearXNG metasearch engine
"""

from typing import List, Optional, Dict, Any
from dataclasses import dataclass
import time
import requests
from urllib.parse import quote, urlencode


@dataclass
class SearchResult:
    """Search result"""
    title: str
    url: str
    snippet: str
    rank: int
    source: str  # searxng, google, bing, etc.
    engine: str  # Original engine name
    category: Optional[str] = None
    score: Optional[float] = None
    published_date: Optional[str] = None
    thumbnail: Optional[str] = None


class SearXNGExecutor:
    """
    Search executor for executing web searches via SearXNG.
    
    SearXNG is a privacy-respecting metasearch engine that aggregates
    results from multiple sources without tracking users.
    """
    
    def __init__(
        self,
        searxng_url: str = "https://searx.be",
        timeout: int = 10,
        max_results: int = 10
    ):
        """
        Initialize SearXNG executor.
        
        Args:
            searxng_url: SearXNG instance URL (default: public instance)
            timeout: Request timeout in seconds
            max_results: Maximum number of results to return
        """
        self.searxng_url = searxng_url.rstrip("/")
        self.timeout = timeout
        self.max_results = max_results
    
    def search(
        self,
        query: str,
        max_results: Optional[int] = None,
        engines: Optional[List[str]] = None,
        categories: Optional[List[str]] = None,
        language: str = "en",
        time_range: Optional[str] = None,
        safesearch: int = 1  # 0=off, 1=moderate, 2=strict
    ) -> List[SearchResult]:
        """
        Execute web search via SearXNG.
        
        Args:
            query: Search query
            max_results: Maximum number of results (defaults to instance default)
            engines: List of specific engines to use (None = use all)
            categories: List of categories (general, images, videos, news, etc.)
            language: Language code (ISO 639-1, default: "en")
            time_range: Time range filter (day, week, month, year)
            safesearch: SafeSearch level (0=off, 1=moderate, 2=strict)
            
        Returns:
            List of search results
        """
        max_results = max_results or self.max_results
        
        # Build SearXNG API URL
        params = {
            "q": query,
            "format": "json",
            "pageno": 1,
            "language": language,
            "safesearch": safesearch,
        }
        
        if max_results:
            params["num"] = max_results
        
        if engines:
            params["engines"] = ",".join(engines)
        
        if categories:
            params["categories"] = ",".join(categories)
        
        if time_range:
            params["time_range"] = time_range
        
        url = f"{self.searxng_url}/search"
        
        try:
            headers = {
                "Accept": "application/json",
                "User-Agent": "Nexus-WebSearch-Agent/1.0",
            }
            
            response = requests.get(
                url,
                params=params,
                headers=headers,
                timeout=self.timeout
            )
            response.raise_for_status()
            
            # Parse JSON response
            data = response.json()
            
            # Transform to SearchResult list
            results = self._parse_searxng_response(data, max_results)
            return results
            
        except requests.exceptions.RequestException as e:
            # Fallback: return empty results with error info
            print(f"SearXNG search error: {e}")
            return []
        except Exception as e:
            print(f"SearXNG parse error: {e}")
            return []
    
    def _parse_searxng_response(
        self,
        data: Dict[str, Any],
        max_results: int
    ) -> List[SearchResult]:
        """
        Parse SearXNG JSON response.
        
        Args:
            data: JSON response data
            max_results: Maximum number of results
            
        Returns:
            List of SearchResult
        """
        results = []
        
        # Parse results array
        items = data.get("results", [])
        
        for i, item in enumerate(items[:max_results]):
            result = SearchResult(
                title=item.get("title", ""),
                url=item.get("url", ""),
                snippet=item.get("content", ""),
                rank=i + 1,
                source="searxng",
                engine=item.get("engine", "unknown"),
                category=item.get("category"),
                score=item.get("score"),
                published_date=item.get("publishedDate"),
                thumbnail=item.get("thumbnail")
            )
            results.append(result)
        
        return results
    
    def search_web(
        self,
        query: str,
        max_results: Optional[int] = None
    ) -> List[SearchResult]:
        """
        Search web (general category).
        
        Args:
            query: Search query
            max_results: Maximum number of results
            
        Returns:
            List of search results
        """
        return self.search(
            query=query,
            max_results=max_results,
            categories=["general"]
        )
    
    def search_images(
        self,
        query: str,
        max_results: Optional[int] = None
    ) -> List[SearchResult]:
        """
        Search images.
        
        Args:
            query: Search query
            max_results: Maximum number of results
            
        Returns:
            List of image search results
        """
        return self.search(
            query=query,
            max_results=max_results,
            categories=["images"]
        )
    
    def search_videos(
        self,
        query: str,
        max_results: Optional[int] = None
    ) -> List[SearchResult]:
        """
        Search videos.
        
        Args:
            query: Search query
            max_results: Maximum number of results
            
        Returns:
            List of video search results
        """
        return self.search(
            query=query,
            max_results=max_results,
            categories=["videos"]
        )
    
    def search_news(
        self,
        query: str,
        max_results: Optional[int] = None
    ) -> List[SearchResult]:
        """
        Search news.
        
        Args:
            query: Search query
            max_results: Maximum number of results
            
        Returns:
            List of news search results
        """
        return self.search(
            query=query,
            max_results=max_results,
            categories=["news"]
        )
    
    def search_code(
        self,
        query: str,
        max_results: Optional[int] = None
    ) -> List[SearchResult]:
        """
        Search code repositories.
        
        Args:
            query: Search query
            max_results: Maximum number of results
            
        Returns:
            List of code search results
        """
        return self.search(
            query=query,
            max_results=max_results,
            categories=["it"],
            engines=["github", "gitlab", "codeberg"]
        )
