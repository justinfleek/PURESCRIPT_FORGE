"""
Pydantic Validation Schemas

Input schemas for various tool types with built-in sanitization.
"""

from typing import Any

from pydantic import BaseModel, ConfigDict, Field, field_validator, model_validator

from toolbox.core.effects import idempotent, monotonic, MonotonicDirection

from .constants import MAX_NESTED_DEPTH, MAX_PROMPT_LENGTH, MAX_TEXT_LENGTH, MAX_URL_LENGTH
from .injection import InjectionRisk, detect_injection
from .sanitizers import sanitize_text


class ToolInputBase(BaseModel):
    """Base class for all tool input schemas."""

    model_config = ConfigDict(
        str_strip_whitespace=True,
        str_max_length=MAX_TEXT_LENGTH,
        validate_assignment=True,
        extra="forbid",  # Reject unknown fields
    )


class LLMInput(ToolInputBase):
    """Input schema for LLM tools."""

    prompt: str = Field(
        ...,
        min_length=1,
        max_length=MAX_PROMPT_LENGTH,
        description="The prompt to send to the LLM",
    )
    system_prompt: str | None = Field(
        None,
        max_length=MAX_PROMPT_LENGTH,
        description="Optional system prompt",
    )
    max_tokens: int = Field(
        default=1000,
        ge=1,
        le=100_000,
        description="Maximum tokens to generate",
    )
    temperature: float = Field(
        default=0.7,
        ge=0.0,
        le=2.0,
        description="Sampling temperature",
    )
    model: str = Field(
        default="default",
        max_length=100,
        description="Model identifier",
    )

    @field_validator("prompt", "system_prompt", mode="before")
    @classmethod
    @idempotent
    def sanitize_prompts(cls, v: Any) -> str | None:
        """
        Sanitize prompt text.
        
        Idempotent: sanitize(sanitize(x)) = sanitize(x)
        """
        if v is None:
            return v
        return sanitize_text(str(v), max_length=MAX_PROMPT_LENGTH)

    @model_validator(mode="after")
    @monotonic(direction=MonotonicDirection.INCREASING)
    def check_injection(self):
        """
        Check for prompt injection attempts.
        
        Monotonic: Security level only increases (never decreases)
        """
        # Check prompt for injection - block ANY detected pattern (enterprise security)
        risk, patterns = detect_injection(self.prompt)
        if risk != InjectionRisk.NONE:
            raise ValueError(f"Potential prompt injection detected: {patterns}")

        # Check system prompt - same strict standard
        if self.system_prompt:
            risk, patterns = detect_injection(self.system_prompt)
            if risk != InjectionRisk.NONE:
                raise ValueError(f"Potential injection in system prompt: {patterns}")

        return self


class TwitterInput(ToolInputBase):
    """Input schema for Twitter tools."""

    content: str = Field(
        ...,
        min_length=1,
        max_length=280,
        description="Tweet content",
    )
    reply_to: str | None = Field(
        None,
        pattern=r"^\d+$",
        description="Tweet ID to reply to",
    )
    media_urls: list[str] = Field(
        default_factory=list,
        max_length=4,
        description="Media URLs to attach",
    )

    @field_validator("content", mode="before")
    @classmethod
    @idempotent
    def sanitize_content(cls, v: Any) -> str:
        """
        Sanitize content text.
        
        Idempotent: sanitize(sanitize(x)) = sanitize(x)
        """
        return sanitize_text(str(v), max_length=280, allow_newlines=True)

    @field_validator("media_urls", mode="before")
    @classmethod
    @idempotent
    def validate_urls(cls, v: Any) -> list[str]:
        """
        Validate and sanitize media URLs.
        
        Idempotent: validate(validate(x)) = validate(x)
        """
        if not v:
            return []
        validated: list[str] = []
        url_list: list[Any] = list(v)[:4] if v else []
        for url in url_list:  # Max 4 media
            url_str = str(url)
            if len(url_str) > MAX_URL_LENGTH:
                continue
            if not url_str.startswith(("http://", "https://")):
                continue
            validated.append(url_str)
        return validated


class SearchInput(ToolInputBase):
    """Input schema for search tools."""

    query: str = Field(
        ...,
        min_length=1,
        max_length=500,
        description="Search query",
    )
    limit: int = Field(
        default=10,
        ge=1,
        le=100,
        description="Maximum results to return",
    )
    filters: dict[str, Any] = Field(
        default_factory=dict,
        description="Optional filters",
    )

    @field_validator("query", mode="before")
    @classmethod
    @idempotent
    def sanitize_query(cls, v: Any) -> str:
        """
        Sanitize search query.
        
        Idempotent: sanitize(sanitize(x)) = sanitize(x)
        """
        return sanitize_text(str(v), max_length=500)

    @model_validator(mode="after")
    def limit_filter_depth(self) -> "SearchInput":
        # Prevent deeply nested filter objects
        def check_depth(obj: Any, depth: int = 0) -> None:
            if depth > MAX_NESTED_DEPTH:
                raise ValueError(f"Filter nesting exceeds maximum depth of {MAX_NESTED_DEPTH}")
            if isinstance(obj, dict):
                for val in obj.values():
                    check_depth(val, depth + 1)
            elif isinstance(obj, list):
                for item in obj:
                    check_depth(item, depth + 1)

        check_depth(self.filters)
        return self


class ContentInput(ToolInputBase):
    """Input schema for content creation tools."""

    title: str = Field(
        ...,
        min_length=1,
        max_length=500,
        description="Content title",
    )
    body: str = Field(
        ...,
        min_length=1,
        max_length=MAX_TEXT_LENGTH,
        description="Content body",
    )
    content_type: str = Field(
        default="post",
        pattern=r"^(post|article|tweet|thread|comment)$",
        description="Type of content",
    )
    tags: list[str] = Field(
        default_factory=list,
        max_length=20,
        description="Content tags",
    )
    metadata: dict[str, Any] = Field(
        default_factory=dict,
        description="Additional metadata",
    )

    @field_validator("title", "body", mode="before")
    @classmethod
    @idempotent
    def sanitize_text_fields(cls, v: Any) -> str:
        """
        Sanitize text fields.
        
        Idempotent: sanitize(sanitize(x)) = sanitize(x)
        """
        return sanitize_text(str(v))

    @field_validator("tags", mode="before")
    @classmethod
    @idempotent
    def sanitize_tags(cls, v: Any) -> list[str]:
        """
        Sanitize content tags.
        
        Idempotent: sanitize(sanitize(x)) = sanitize(x)
        """
        if not v:
            return []
        tag_list: list[Any] = list(v)[:20] if v else []
        return [sanitize_text(str(tag), max_length=50, allow_newlines=False) for tag in tag_list]


class ImageGenInput(ToolInputBase):
    """Input schema for image generation tools."""

    prompt: str = Field(
        ...,
        min_length=1,
        max_length=2000,
        description="Image generation prompt",
    )
    negative_prompt: str = Field(
        default="",
        max_length=1000,
        description="Negative prompt",
    )
    width: int = Field(
        default=1024,
        ge=64,
        le=4096,
        description="Image width",
    )
    height: int = Field(
        default=1024,
        ge=64,
        le=4096,
        description="Image height",
    )
    steps: int = Field(
        default=20,
        ge=1,
        le=150,
        description="Diffusion steps",
    )
    seed: int | None = Field(
        None,
        ge=0,
        description="Random seed for reproducibility",
    )

    @field_validator("prompt", "negative_prompt", mode="before")
    @classmethod
    @idempotent
    def sanitize_prompts(cls, v: Any) -> str:
        """
        Sanitize prompt text for image generation.
        
        Idempotent: sanitize(sanitize(x)) = sanitize(x)
        """
        if v is None:
            return ""
        return sanitize_text(str(v), max_length=2000)

    @model_validator(mode="after")
    def check_dimensions(self):
        # Limit total pixels to prevent memory issues
        if self.width * self.height > 16_000_000:  # 16 megapixels
            raise ValueError("Image dimensions exceed maximum (16 megapixels)")
        return self
