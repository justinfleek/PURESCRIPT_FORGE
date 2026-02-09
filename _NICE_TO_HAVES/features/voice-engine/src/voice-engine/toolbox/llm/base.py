"""
LLM Base Types - Minimal implementation for voice engine.
"""

from dataclasses import dataclass
from enum import Enum
from typing import Literal, Final

from toolbox.fields import Bounds

# Bounds
BOUNDS_TEMPERATURE = Bounds(min=0.0, max=2.0)
BOUNDS_TOP_P = Bounds(min=0.0, max=1.0)


class AnalystRole(Enum):
    """Analyst roles."""
    GENERAL_ASSISTANT = "general_assistant"
    CONTENT_STRATEGIST = "content_strategist"
    COPYWRITER = "copywriter"
    SEO_SPECIALIST = "seo_specialist"
    EMAIL_SPECIALIST = "email_specialist"
    DATA_ANALYST = "data_analyst"
    BRAND_VOICE = "brand_voice"
    CAMPAIGN_PLANNER = "campaign_planner"
    AUTOMATION_ENGINEER = "automation_engineer"
    AUDIENCE_ANALYST = "audience_analyst"
    SEGMENTATION_EXPERT = "segmentation_expert"
    PERSONALIZATION_EXPERT = "personalization_expert"
    ATTRIBUTION_ANALYST = "attribution_analyst"
    INSIGHTS_GENERATOR = "insights_generator"
    FORECASTER = "forecaster"
    MEDIA_BUYER = "media_buyer"
    CREATIVE_ANALYST = "creative_analyst"
    AD_COPYWRITER = "ad_copywriter"
    SALES_ANALYST = "sales_analyst"
    LEAD_SCORER = "lead_scorer"
    COMPETITIVE_ANALYST = "competitive_analyst"
    SOCIAL_MANAGER = "social_manager"
    COMMUNITY_MANAGER = "community_manager"
    INFLUENCER_ANALYST = "influencer_analyst"
    RESEARCH_ANALYST = "research_analyst"


@dataclass(frozen=True)
class AnalystSpec:
    """Analyst specification."""
    role: AnalystRole
    name: str
    description: str = ""
    system_prompt: str = ""
    preferred_model: str = "gpt-4o"
    fallback_model: str = "gpt-4o-mini"
    temperature: float = 0.7
    max_tokens: int = 4096
    allowed_tools: tuple[str, ...] = ()
    modules: tuple[str, ...] = ()
    expertise: tuple[str, ...] = ()
    max_cost_per_request_usd: float = 1.0

__all__ = ["AnalystRole", "AnalystSpec", "BOUNDS_TEMPERATURE", "BOUNDS_TOP_P"]
