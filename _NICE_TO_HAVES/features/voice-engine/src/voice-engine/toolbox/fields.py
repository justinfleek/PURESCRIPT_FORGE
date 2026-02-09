"""
Field Bounds - Minimal implementation for voice engine.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class Bounds:
    """Bounds for numeric values."""
    min: float
    max: float
    
    def contains(self, value: float) -> bool:
        """Check if value is within bounds."""
        return self.min <= value <= self.max

__all__ = ["Bounds"]
