"""
Nexus Web Search Agent - Link Follower
Follow links from search results and fetch content
"""

from typing import List, Optional
from dataclasses import dataclass
import requests
from urllib.parse import urljoin, urlparse
import time


@dataclass
class WebContent:
    """Web content"""
    url: str
    content_type: str  # html, pdf, text, etc.
    content: str  # Full content or path to file
    title: Optional[str] = None
    metadata: Optional[dict] = None


class LinkFollower:
    """
    Link follower for following links from search results.
    
    Fetches web content from URLs and extracts links.
    """
    
    def __init__(self, timeout: int = 10, max_content_size: int = 10 * 1024 * 1024):
        """
        Initialize link follower.
        
        Args:
            timeout: Request timeout in seconds
            max_content_size: Maximum content size in bytes
        """
        self.timeout = timeout
        self.max_content_size = max_content_size
    
    def follow_link(self, url: str) -> Optional[WebContent]:
        """
        Follow link and fetch content.
        
        Args:
            url: URL to fetch
            
        Returns:
            Web content or None if fetch failed
        """
        try:
            headers = {
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"
            }
            
            response = requests.get(
                url,
                headers=headers,
                timeout=self.timeout,
                stream=True,
                allow_redirects=True
            )
            response.raise_for_status()
            
            # Check content size
            content_length = response.headers.get("Content-Length")
            if content_length and int(content_length) > self.max_content_size:
                return None  # Too large
            
            # Read content
            content = response.text[:self.max_content_size]  # Limit size
            
            # Determine content type
            content_type = self._determine_content_type(response.headers, url)
            
            # Extract title (simplified - would use HTML parser in production)
            title = self._extract_title(content, content_type)
            
            return WebContent(
                url=url,
                content_type=content_type,
                content=content,
                title=title,
                metadata={
                    "status_code": response.status_code,
                    "content_length": len(content),
                    "headers": dict(response.headers)
                }
            )
            
        except Exception as e:
            print(f"Error fetching {url}: {e}")
            return None
    
    def extract_links(self, content: WebContent) -> List[str]:
        """
        Extract links from web content.
        
        Args:
            content: Web content
            
        Returns:
            List of URLs
        """
        if content.content_type != "html":
            return []
        
        # Simple regex-based extraction (would use HTML parser in production)
        import re
        
        # Find all href attributes
        href_pattern = r'href=["\']([^"\']+)["\']'
        matches = re.findall(href_pattern, content.content)
        
        # Convert relative URLs to absolute
        links = []
        base_url = content.url
        
        for match in matches:
            # Skip javascript:, mailto:, etc.
            if match.startswith(("javascript:", "mailto:", "#")):
                continue
            
            # Convert to absolute URL
            absolute_url = urljoin(base_url, match)
            links.append(absolute_url)
        
        return links
    
    def _determine_content_type(self, headers: dict, url: str) -> str:
        """
        Determine content type from headers or URL.
        
        Args:
            headers: HTTP headers
            url: URL
            
        Returns:
            Content type (html, pdf, text, etc.)
        """
        # Check Content-Type header
        content_type = headers.get("Content-Type", "").lower()
        
        if "text/html" in content_type:
            return "html"
        elif "application/pdf" in content_type:
            return "pdf"
        elif "text/plain" in content_type:
            return "text"
        elif "application/json" in content_type:
            return "json"
        
        # Fallback: check URL extension
        url_lower = url.lower()
        if url_lower.endswith(".pdf"):
            return "pdf"
        elif url_lower.endswith(".html") or url_lower.endswith(".htm"):
            return "html"
        elif url_lower.endswith(".txt"):
            return "text"
        elif url_lower.endswith(".json"):
            return "json"
        
        # Default to html
        return "html"
    
    def _extract_title(self, content: str, content_type: str) -> Optional[str]:
        """
        Extract title from content.
        
        Args:
            content: Content string
            content_type: Content type
            
        Returns:
            Title or None
        """
        if content_type != "html":
            return None
        
        # Simple regex extraction (would use HTML parser in production)
        import re
        
        # Find <title> tag
        title_match = re.search(r'<title[^>]*>([^<]+)</title>', content, re.IGNORECASE)
        if title_match:
            return title_match.group(1).strip()
        
        # Fallback: find <h1> tag
        h1_match = re.search(r'<h1[^>]*>([^<]+)</h1>', content, re.IGNORECASE)
        if h1_match:
            return h1_match.group(1).strip()
        
        return None
