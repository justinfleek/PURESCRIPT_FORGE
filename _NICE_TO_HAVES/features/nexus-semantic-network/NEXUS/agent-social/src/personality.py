"""
Nexus Agent Social - Personality System
Agent personality/identity system for social interactions
"""

from typing import Dict, List
from dataclasses import dataclass, field
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent / "agent-social" / "src"))
from agent_profile import AgentProfile


@dataclass
class Personality:
    """Agent personality"""
    agent_id: str
    traits: Dict[str, float] = field(default_factory=dict)  # trait -> strength (0-1)
    communication_style: str = "neutral"  # formal, casual, technical, creative
    content_preferences: List[str] = field(default_factory=list)
    interaction_frequency: float = 0.5  # How often agent interacts (0-1)
    exploration_tendency: float = 0.5  # How much agent explores (0-1)
    social_tendency: float = 0.5  # How social agent is (0-1)


class PersonalityGenerator:
    """
    Personality generator for generating agent personalities.
    
    Generates diverse personalities with:
    - Big Five traits (Openness, Conscientiousness, Extraversion, Agreeableness, Neuroticism)
    - Communication style
    - Content preferences
    - Interaction patterns
    """
    
    def __init__(self):
        """Initialize personality generator"""
        self.trait_names = [
            "openness", "conscientiousness", "extraversion",
            "agreeableness", "neuroticism",
            "curiosity", "creativity", "analytical",
            "social", "introverted", "adventurous",
            "cautious", "optimistic", "pessimistic",
            "empathetic", "logical", "artistic"
        ]
        
        self.communication_styles = [
            "formal", "casual", "technical", "creative",
            "humorous", "serious", "enthusiastic", "reserved"
        ]
    
    def generate_personality(self, agent_id: str) -> Personality:
        """
        Generate personality for agent.
        
        Args:
            agent_id: Agent ID
            
        Returns:
            Personality
        """
        # Generate Big Five traits
        traits = {
            "openness": random.uniform(0.0, 1.0),
            "conscientiousness": random.uniform(0.0, 1.0),
            "extraversion": random.uniform(0.0, 1.0),
            "agreeableness": random.uniform(0.0, 1.0),
            "neuroticism": random.uniform(0.0, 1.0),
        }
        
        # Generate additional traits
        for trait in ["curiosity", "creativity", "analytical", "social", "adventurous"]:
            traits[trait] = random.uniform(0.0, 1.0)
        
        # Determine communication style based on traits
        communication_style = self._determine_communication_style(traits)
        
        # Determine content preferences
        content_preferences = self._determine_content_preferences(traits)
        
        # Determine interaction patterns
        interaction_frequency = traits.get("extraversion", 0.5)
        exploration_tendency = traits.get("openness", 0.5)
        social_tendency = traits.get("extraversion", 0.5) * traits.get("agreeableness", 0.5)
        
        return Personality(
            agent_id=agent_id,
            traits=traits,
            communication_style=communication_style,
            content_preferences=content_preferences,
            interaction_frequency=interaction_frequency,
            exploration_tendency=exploration_tendency,
            social_tendency=social_tendency
        )
    
    def _determine_communication_style(self, traits: Dict[str, float]) -> str:
        """
        Determine communication style from traits.
        
        Args:
            traits: Personality traits
            
        Returns:
            Communication style
        """
        extraversion = traits.get("extraversion", 0.5)
        creativity = traits.get("creativity", 0.5)
        analytical = traits.get("analytical", 0.5)
        
        if analytical > 0.7:
            return "technical"
        elif creativity > 0.7:
            return "creative"
        elif extraversion > 0.7:
            return "enthusiastic"
        elif extraversion < 0.3:
            return "reserved"
        elif creativity > 0.5:
            return "humorous"
        else:
            return "casual"
    
    def _determine_content_preferences(self, traits: Dict[str, float]) -> List[str]:
        """
        Determine content preferences from traits.
        
        Args:
            traits: Personality traits
            
        Returns:
            List of content preferences
        """
        preferences = []
        
        openness = traits.get("openness", 0.5)
        creativity = traits.get("creativity", 0.5)
        analytical = traits.get("analytical", 0.5)
        social = traits.get("social", 0.5)
        
        if openness > 0.7:
            preferences.append("exploration")
            preferences.append("discovery")
        
        if creativity > 0.7:
            preferences.append("artistic")
            preferences.append("creative")
        
        if analytical > 0.7:
            preferences.append("technical")
            preferences.append("research")
        
        if social > 0.7:
            preferences.append("social")
            preferences.append("community")
        
        if not preferences:
            preferences.append("general")
        
        return preferences
    
    def influence_post_creation(
        self,
        personality: Personality,
        base_content: str
    ) -> str:
        """
        Influence post content based on personality.
        
        Args:
            personality: Agent personality
            base_content: Base content
            
        Returns:
            Modified content
        """
        # Modify content based on communication style
        style = personality.communication_style
        
        if style == "formal":
            # Make more formal
            content = base_content.capitalize()
        elif style == "casual":
            # Make more casual
            content = base_content.lower()
        elif style == "humorous":
            # Add humor markers
            content = f"{base_content} 😄"
        elif style == "enthusiastic":
            # Add enthusiasm
            content = f"{base_content}!"
        else:
            content = base_content
        
        return content
    
    def influence_interaction_decision(
        self,
        personality: Personality,
        post: "AgentPost"
    ) -> bool:
        """
        Decide whether agent should interact with post based on personality.
        
        Args:
            personality: Agent personality
            post: Post to potentially interact with
            
        Returns:
            True if should interact
        """
        # Base probability from interaction frequency
        prob = personality.interaction_frequency
        
        # Adjust based on content preferences
        if any(pref in post.tags for pref in personality.content_preferences):
            prob += 0.2
        
        # Adjust based on social tendency
        if post.stats.get("likes_count", 0) > 10:
            prob += personality.social_tendency * 0.1
        
        return random.random() < prob
