"""
Nexus Performance - Caching Layer
Caching and performance optimizations
"""

from typing import Dict, Optional, Any, Callable
from datetime import datetime, timedelta
from functools import wraps
import hashlib
import json


class Cache:
    """
    Simple in-memory cache with TTL.
    
    Caches:
    - Database queries
    - Network graph computations
    - Agent profiles
    - Feed data
    """
    
    def __init__(self, default_ttl_seconds: int = 300):
        """
        Initialize cache.
        
        Args:
            default_ttl_seconds: Default TTL in seconds
        """
        self.cache: Dict[str, tuple] = {}  # key -> (value, expiry_time)
        self.default_ttl = default_ttl_seconds
    
    def get(self, key: str) -> Optional[Any]:
        """
        Get value from cache.
        
        Args:
            key: Cache key
            
        Returns:
            Cached value or None
        """
        if key not in self.cache:
            return None
        
        value, expiry = self.cache[key]
        
        # Check if expired
        if datetime.utcnow() > expiry:
            del self.cache[key]
            return None
        
        return value
    
    def set(self, key: str, value: Any, ttl_seconds: Optional[int] = None) -> None:
        """
        Set value in cache.
        
        Args:
            key: Cache key
            value: Value to cache
            ttl_seconds: TTL in seconds (uses default if None)
        """
        ttl = ttl_seconds or self.default_ttl
        expiry = datetime.utcnow() + timedelta(seconds=ttl)
        self.cache[key] = (value, expiry)
    
    def delete(self, key: str) -> None:
        """
        Delete key from cache.
        
        Args:
            key: Cache key
        """
        if key in self.cache:
            del self.cache[key]
    
    def clear(self) -> None:
        """Clear all cache"""
        self.cache.clear()
    
    def cleanup_expired(self) -> int:
        """
        Clean up expired entries.
        
        Returns:
            Number of entries removed
        """
        now = datetime.utcnow()
        expired_keys = [
            key for key, (_, expiry) in self.cache.items()
            if now > expiry
        ]
        
        for key in expired_keys:
            del self.cache[key]
        
        return len(expired_keys)


def cached(ttl_seconds: int = 300):
    """
    Decorator for caching function results.
    
    Args:
        ttl_seconds: TTL in seconds
        
    Returns:
        Decorated function
    """
    def decorator(func: Callable) -> Callable:
        cache = Cache(ttl_seconds=ttl_seconds)
        
        @wraps(func)
        def wrapper(*args, **kwargs):
            # Generate cache key from function name and arguments
            key_parts = [func.__name__]
            key_parts.extend(str(arg) for arg in args)
            key_parts.extend(f"{k}={v}" for k, v in sorted(kwargs.items()))
            key_str = json.dumps(key_parts, sort_keys=True)
            key_hash = hashlib.md5(key_str.encode()).hexdigest()
            
            # Check cache
            cached_value = cache.get(key_hash)
            if cached_value is not None:
                return cached_value
            
            # Compute and cache
            result = func(*args, **kwargs)
            cache.set(key_hash, result, ttl_seconds)
            return result
        
        return wrapper
    return decorator


class QueryCache:
    """
    Cache for database queries.
    """
    
    def __init__(self):
        """Initialize query cache"""
        self.cache = Cache(default_ttl_seconds=60)  # 1 minute TTL for queries
    
    def get_query_result(self, query: str, params: tuple) -> Optional[Any]:
        """
        Get cached query result.
        
        Args:
            query: SQL query
            params: Query parameters
            
        Returns:
            Cached result or None
        """
        key = self._make_key(query, params)
        return self.cache.get(key)
    
    def set_query_result(self, query: str, params: tuple, result: Any) -> None:
        """
        Cache query result.
        
        Args:
            query: SQL query
            params: Query parameters
            result: Query result
        """
        key = self._make_key(query, params)
        self.cache.set(key, result)
    
    def _make_key(self, query: str, params: tuple) -> str:
        """
        Make cache key from query and params.
        
        Args:
            query: SQL query
            params: Query parameters
            
        Returns:
            Cache key
        """
        key_str = f"{query}:{params}"
        return hashlib.md5(key_str.encode()).hexdigest()
