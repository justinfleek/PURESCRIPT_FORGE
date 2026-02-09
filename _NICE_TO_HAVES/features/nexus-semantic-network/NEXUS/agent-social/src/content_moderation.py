"""
Nexus Agent Social - Content Moderation
Content moderation and filtering
"""

from typing import List, Dict, Optional
from dataclasses import dataclass
import re


@dataclass
class ModerationResult:
    """Content moderation result"""
    is_safe: bool
    reason: str
    flagged_keywords: List[str] = None
    confidence: float = 1.0  # 0.0 to 1.0


class ContentModerator:
    """
    Content moderator for filtering inappropriate content.
    
    Filters:
    - Spam patterns
    - Inappropriate language
    - Malicious links
    - Excessive repetition
    """
    
    def __init__(self):
        """Initialize content moderator"""
        # Spam patterns
        self.spam_patterns = [
            r'\b(buy\s+now|click\s+here|limited\s+time|act\s+now)\b',
            r'\b(free\s+money|make\s+money\s+fast|get\s+rich)\b',
            r'(.)\1{10,}',  # Excessive character repetition
        ]
        
        # Inappropriate keywords (simplified - would use ML in production)
        self.inappropriate_keywords = [
            # Would be loaded from config/database
        ]
        
        # Link patterns
        self.suspicious_link_patterns = [
            r'bit\.ly',
            r'tinyurl\.com',
            r'short\.link',
        ]
    
    def moderate_content(self, content: str) -> ModerationResult:
        """
        Moderate content for safety.
        
        Args:
            content: Content to moderate
            
        Returns:
            Moderation result
        """
        # Check spam patterns
        spam_result = self._check_spam(content)
        if not spam_result.is_safe:
            return spam_result
        
        # Check inappropriate keywords
        keyword_result = self._check_keywords(content)
        if not keyword_result.is_safe:
            return keyword_result
        
        # Check suspicious links
        link_result = self._check_links(content)
        if not link_result.is_safe:
            return link_result
        
        # Check length (very long posts might be spam)
        if len(content) > 10000:
            return ModerationResult(
                is_safe=False,
                reason="Content too long",
                confidence=0.7
            )
        
        return ModerationResult(
            is_safe=True,
            reason="Content passed moderation",
            confidence=1.0
        )
    
    def _check_spam(self, content: str) -> ModerationResult:
        """
        Check for spam patterns.
        
        Args:
            content: Content to check
            
        Returns:
            Moderation result
        """
        flagged_keywords = []
        
        for pattern in self.spam_patterns:
            matches = re.findall(pattern, content, re.IGNORECASE)
            if matches:
                flagged_keywords.extend(matches)
        
        if flagged_keywords:
            return ModerationResult(
                is_safe=False,
                reason="Spam detected",
                flagged_keywords=flagged_keywords,
                confidence=0.8
            )
        
        return ModerationResult(is_safe=True, reason="No spam detected")
    
    def _check_keywords(self, content: str) -> ModerationResult:
        """
        Check for inappropriate keywords.
        
        Args:
            content: Content to check
            
        Returns:
            Moderation result
        """
        content_lower = content.lower()
        flagged_keywords = []
        
        for keyword in self.inappropriate_keywords:
            if keyword.lower() in content_lower:
                flagged_keywords.append(keyword)
        
        if flagged_keywords:
            return ModerationResult(
                is_safe=False,
                reason="Inappropriate keywords detected",
                flagged_keywords=flagged_keywords,
                confidence=0.9
            )
        
        return ModerationResult(is_safe=True, reason="No inappropriate keywords")
    
    def _check_links(self, content: str) -> ModerationResult:
        """
        Check for suspicious links.
        
        Args:
            content: Content to check
            
        Returns:
            Moderation result
        """
        flagged_links = []
        
        for pattern in self.suspicious_link_patterns:
            matches = re.findall(pattern, content, re.IGNORECASE)
            if matches:
                flagged_links.extend(matches)
        
        if flagged_links:
            return ModerationResult(
                is_safe=False,
                reason="Suspicious links detected",
                flagged_keywords=flagged_links,
                confidence=0.7
            )
        
        return ModerationResult(is_safe=True, reason="No suspicious links")
    
    def filter_content(self, content: str) -> str:
        """
        Filter inappropriate content from text.
        
        Args:
            content: Content to filter
            
        Returns:
            Filtered content
        """
        # Remove inappropriate keywords
        filtered = content
        for keyword in self.inappropriate_keywords:
            filtered = re.sub(
                re.escape(keyword),
                "[FILTERED]",
                filtered,
                flags=re.IGNORECASE
            )
        
        return filtered
