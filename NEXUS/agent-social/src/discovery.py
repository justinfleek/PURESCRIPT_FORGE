"""
Nexus Agent Social - Discovery
Agent discovery and recommendations for social network
"""

from typing import List, Dict, Set
from dataclasses import dataclass
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent / "agent-social" / "src"))
from agent_profile import AgentProfileManager, AgentProfile


@dataclass
class Recommendation:
    """Agent recommendation"""
    agent_id: str
    reason: str
    score: float  # 0.0 to 1.0
    metadata: Dict = None


class AgentDiscovery:
    """
    Agent discovery for finding and recommending agents.
    
    Discovers agents based on:
    - Shared interests
    - Mutual connections
    - Similar expertise
    - Content similarity
    - Network proximity
    """
    
    def __init__(self, profile_manager: AgentProfileManager):
        """
        Initialize agent discovery.
        
        Args:
            profile_manager: Agent profile manager
        """
        self.profile_manager = profile_manager
    
    def discover_agents(
        self,
        agent_id: str,
        limit: int = 10
    ) -> List[Recommendation]:
        """
        Discover agents for recommendation.
        
        Args:
            agent_id: Agent ID
            limit: Maximum number of recommendations
            
        Returns:
            List of recommendations
        """
        profile = self.profile_manager.get_profile(agent_id)
        if not profile:
            return []
        
        recommendations = []
        all_profiles = list(self.profile_manager.profiles.values())
        
        for candidate in all_profiles:
            if candidate.agent_id == agent_id:
                continue
            
            # Skip if already following
            if candidate.agent_id in self.profile_manager.follows.get(agent_id, set()):
                continue
            
            # Calculate recommendation score
            score, reasons = self._calculate_recommendation_score(profile, candidate)
            
            if score > 0.3:  # Threshold
                recommendations.append(Recommendation(
                    agent_id=candidate.agent_id,
                    reason=", ".join(reasons),
                    score=score,
                    metadata={
                        "shared_interests": len(set(profile.interests) & set(candidate.interests)),
                        "shared_expertise": len(set(profile.expertise) & set(candidate.expertise))
                    }
                ))
        
        # Sort by score
        recommendations.sort(key=lambda r: r.score, reverse=True)
        
        return recommendations[:limit]
    
    def _calculate_recommendation_score(
        self,
        profile: AgentProfile,
        candidate: AgentProfile
    ) -> tuple:
        """
        Calculate recommendation score for candidate.
        
        Args:
            profile: Agent profile
            candidate: Candidate agent profile
            
        Returns:
            (score, reasons) tuple
        """
        score = 0.0
        reasons = []
        
        # Shared interests (0.4 weight)
        shared_interests = set(profile.interests) & set(candidate.interests)
        if shared_interests:
            interest_score = len(shared_interests) / max(len(profile.interests), 1)
            score += 0.4 * interest_score
            reasons.append(f"shared {len(shared_interests)} interests")
        
        # Shared expertise (0.3 weight)
        shared_expertise = set(profile.expertise) & set(candidate.expertise)
        if shared_expertise:
            expertise_score = len(shared_expertise) / max(len(profile.expertise), 1)
            score += 0.3 * expertise_score
            reasons.append(f"shared {len(shared_expertise)} expertise areas")
        
        # Mutual connections (0.2 weight)
        mutual_connections = self._count_mutual_connections(profile.agent_id, candidate.agent_id)
        if mutual_connections > 0:
            mutual_score = min(mutual_connections / 10.0, 1.0)
            score += 0.2 * mutual_score
            reasons.append(f"{mutual_connections} mutual connections")
        
        # Popularity boost (0.1 weight)
        followers_count = candidate.stats.get("followers_count", 0)
        popularity_score = min(followers_count / 100.0, 1.0)
        score += 0.1 * popularity_score
        
        return (min(score, 1.0), reasons)
    
    def _count_mutual_connections(self, agent_id1: str, agent_id2: str) -> int:
        """
        Count mutual connections between two agents.
        
        Args:
            agent_id1: First agent ID
            agent_id2: Second agent ID
            
        Returns:
            Number of mutual connections
        """
        follows1 = self.profile_manager.follows.get(agent_id1, set())
        follows2 = self.profile_manager.follows.get(agent_id2, set())
        
        mutual = follows1 & follows2
        return len(mutual)
    
    def discover_by_interests(
        self,
        interests: List[str],
        limit: int = 10
    ) -> List[AgentProfile]:
        """
        Discover agents by interests.
        
        Args:
            interests: List of interests
            limit: Maximum number of results
            
        Returns:
            List of agent profiles
        """
        matches = []
        
        for profile in self.profile_manager.profiles.values():
            shared = set(profile.interests) & set(interests)
            if shared:
                matches.append((len(shared), profile))
        
        # Sort by number of shared interests
        matches.sort(key=lambda x: x[0], reverse=True)
        
        return [profile for _, profile in matches[:limit]]
    
    def discover_by_expertise(
        self,
        expertise: List[str],
        limit: int = 10
    ) -> List[AgentProfile]:
        """
        Discover agents by expertise.
        
        Args:
            expertise: List of expertise areas
            limit: Maximum number of results
            
        Returns:
            List of agent profiles
        """
        matches = []
        
        for profile in self.profile_manager.profiles.values():
            shared = set(profile.expertise) & set(expertise)
            if shared:
                matches.append((len(shared), profile))
        
        # Sort by number of shared expertise areas
        matches.sort(key=lambda x: x[0], reverse=True)
        
        return [profile for _, profile in matches[:limit]]
