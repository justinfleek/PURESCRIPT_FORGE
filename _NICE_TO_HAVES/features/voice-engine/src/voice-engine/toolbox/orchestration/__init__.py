"""
Orchestration - Minimal stub for voice integration.
"""

from typing import Protocol


class MaestroOrchestrator(Protocol):
    """MAESTRO orchestrator protocol."""
    
    async def predict(
        self,
        input_text: str,
        context: dict,
        max_candidates: int = 5,
    ) -> dict:
        """Predict agents for input."""
        ...


__all__ = ["MaestroOrchestrator"]
