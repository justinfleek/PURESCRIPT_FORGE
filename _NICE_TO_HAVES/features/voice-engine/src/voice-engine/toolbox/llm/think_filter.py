"""
Think Filter - Incremental Streaming Filter for Thinking Blocks

Ground Truth: trtllm-serve-main/nix/openai-proxy-hs/ChatTemplate.hs
STRAYLIGHT_STANDARDS: Thinking Block Standards - Incremental Streaming Filter

Filters <think>...</think> blocks from token stream during streaming.

Key Challenge: Tags can be split across tokens!
  Token 1: "Hello <thi"
  Token 2: "nk>reason"
  Token 3: "ing</think>world"

Solution: Buffering potential partial tags
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Literal

THINK_START = "<think>"
THINK_END = "</think>"


class ThinkState(str, Enum):
    """Think filter state"""

    OUTSIDE_THINK = "outside_think"  # Not inside think block, emitting content
    INSIDE_THINK = "inside_think"  # Inside <think>...</think>, discarding content


@dataclass
class ThinkFilter:
    """
    State machine for filtering thinking blocks from token stream.

    STRAYLIGHT_STANDARDS: Incremental Streaming Filter State Machine
    """

    state: ThinkState
    buffer: str  # Buffered text (potential partial tag)

    def __post_init__(self) -> None:
        """Validate filter"""
        if not isinstance(self.state, ThinkState):
            raise TypeError(f"state must be ThinkState, got {type(self.state)}")
        if not isinstance(self.buffer, str):
            raise TypeError(f"buffer must be str, got {type(self.buffer)}")


@dataclass
class ThinkResult:
    """Result from feeding token to filter"""

    filter: ThinkFilter  # Updated filter state
    output: str  # Text to emit (may be empty)


def init_think_filter() -> ThinkFilter:
    """
    Initialize think filter.

    Starts in OutsideThink state (emitting content).

    STRAYLIGHT_STANDARDS: ThinkFilter Initialization
    """
    return ThinkFilter(state=ThinkState.OUTSIDE_THINK, buffer="")


def feed_think_filter(filter: ThinkFilter, token: str) -> ThinkResult:
    """
    Feed token to filter, get output and new state.

    Args:
        filter: Current filter state
        token: Incoming token (may be partial)

    Returns:
        ThinkResult - Updated filter and output to emit

    STRAYLIGHT_STANDARDS: Incremental Streaming Filter Processing

    State Transitions:
        OutsideThink ──<think>──> InsideThink ──</think>──> OutsideThink
             │                         │
             │ (other)                 │ (other)
             ▼                         ▼
          emit token               buffer (discard)
    """
    buffer = filter.buffer + token
    output = ""
    state = filter.state

    while buffer:
        if state == ThinkState.OUTSIDE_THINK:
            # Look for <think> start tag
            think_start_idx = buffer.find(THINK_START)

            if think_start_idx == -1:
                # No <think> found, emit everything
                output += buffer
                buffer = ""
            else:
                # Found <think>, emit content before it
                output += buffer[:think_start_idx]
                buffer = buffer[think_start_idx:]
                state = ThinkState.INSIDE_THINK

        elif state == ThinkState.INSIDE_THINK:
            # Look for </think> end tag
            think_end_idx = buffer.find(THINK_END)

            if think_end_idx == -1:
                # No </think> found, discard everything (might be partial tag)
                buffer = ""
            else:
                # Found </think>, discard up to and including it
                buffer = buffer[think_end_idx + len(THINK_END) :]
                state = ThinkState.OUTSIDE_THINK

    return ThinkResult(
        filter=ThinkFilter(state=state, buffer=buffer), output=output
    )


def finalize_think_filter(filter: ThinkFilter) -> str:
    """
    Finalize filter when stream ends.

    Args:
        filter: Current filter state

    Returns:
        str - Remaining output to emit

    Behavior:
    - If OutsideThink: emit remaining buffer
    - If InsideThink: discard remaining buffer (was thinking)

    STRAYLIGHT_STANDARDS: ThinkFilter Finalization
    """
    if filter.state == ThinkState.OUTSIDE_THINK:
        return filter.buffer
    else:
        # Inside think block - discard
        return ""


__all__ = [
    "ThinkState",
    "ThinkFilter",
    "ThinkResult",
    "init_think_filter",
    "feed_think_filter",
    "finalize_think_filter",
]
