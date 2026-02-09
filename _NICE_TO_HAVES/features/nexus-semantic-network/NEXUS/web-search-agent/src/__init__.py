"""
Nexus Web Search Agent
Autonomous web search based on queries
"""

from .query_generator import QueryGenerator, Query
from .search_executor import SearchExecutor, SearchResult
from .result_ranker import ResultRanker
from .link_follower import LinkFollower, WebContent

# SearXNG executor (preferred)
try:
    from .searxng_executor import SearXNGExecutor
    __all__ = [
        "QueryGenerator",
        "Query",
        "SearchExecutor",
        "SearchResult",
        "SearXNGExecutor",  # Preferred
        "ResultRanker",
        "LinkFollower",
        "WebContent",
    ]
except ImportError:
    __all__ = [
        "QueryGenerator",
        "Query",
        "SearchExecutor",
        "SearchResult",
        "ResultRanker",
        "LinkFollower",
        "WebContent",
    ]
