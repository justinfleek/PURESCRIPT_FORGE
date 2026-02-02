"""
Schema Registry & Validation Entry Point

Maps tool names to validation schemas and provides the main validation interface.
"""

from typing import Any, cast

from toolbox.core.effects import idempotent

from .constants import MAX_LIST_SIZE, MAX_NESTED_DEPTH
from .sanitizers import sanitize_text
from .schemas import (
    ContentInput,
    ImageGenInput,
    LLMInput,
    SearchInput,
    ToolInputBase,
    TwitterInput,
)


# =============================================================================
# Schema Registry
# =============================================================================

TOOL_SCHEMAS: dict[str, type[ToolInputBase]] = {
    "llm:generate": LLMInput,
    "llm:chat": LLMInput,
    "twitter:post": TwitterInput,
    "twitter:reply": TwitterInput,
    "search:web": SearchInput,
    "search:news": SearchInput,
    "content:create": ContentInput,
    "content:update": ContentInput,
    "image:generate": ImageGenInput,
}


def get_schema(tool_name: str) -> type[ToolInputBase] | None:
    """Get the validation schema for a tool."""
    return TOOL_SCHEMAS.get(tool_name)


@idempotent
def validate_input(tool_name: str, params: dict[str, Any]) -> dict[str, Any]:
    """
    Validate and sanitize input for a tool.

    Idempotent: validate(validate(x)) = validate(x)

    Args:
        tool_name: Name of the tool
        params: Raw input parameters

    Returns:
        Validated and sanitized parameters

    Raises:
        ValueError: If validation fails
    """
    schema = get_schema(tool_name)

    if schema is None:
        # No schema defined - apply basic sanitization
        return _sanitize_generic(params)

    # Validate with Pydantic
    validated = schema(**params)
    return validated.model_dump()


@idempotent
def _sanitize_generic(params: dict[str, Any], depth: int = 0) -> dict[str, Any]:
    """
    Apply generic sanitization to untyped params.
    
    Idempotent: sanitize(sanitize(x)) = sanitize(x)
    """
    if depth > MAX_NESTED_DEPTH:
        raise ValueError(f"Input nesting exceeds maximum depth of {MAX_NESTED_DEPTH}")

    result: dict[str, Any] = {}
    for key, value in params.items():
        # Sanitize key
        sanitized_key = sanitize_text(str(key), max_length=100, allow_newlines=False)

        # Sanitize value based on type
        if isinstance(value, str):
            result[sanitized_key] = sanitize_text(value)
        elif isinstance(value, dict):
            dict_value = cast("dict[str, Any]", value)
            result[sanitized_key] = _sanitize_generic(dict_value, depth + 1)
        elif isinstance(value, list):
            value_list = cast("list[Any]", value)
            if len(value_list) > MAX_LIST_SIZE:
                value_list = value_list[:MAX_LIST_SIZE]
            sanitized_list: list[Any] = []
            for v in value_list:
                if isinstance(v, dict):
                    dict_v = cast("dict[str, Any]", v)
                    sanitized_list.append(_sanitize_generic(dict_v, depth + 1))
                elif isinstance(v, str):
                    sanitized_list.append(sanitize_text(v))
                else:
                    sanitized_list.append(v)
            result[sanitized_key] = sanitized_list
        else:
            result[sanitized_key] = value

    return result
