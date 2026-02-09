"""
Nexus Agent Social - Analytics
Network analytics and metrics dashboard
"""

from typing import Dict, List, Optional
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from collections import defaultdict
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent.parent / "agent-social" / "src"))
from agent_profile import AgentProfileManager


@dataclass
class NetworkMetrics:
    """Network-level metrics"""
    total_agents: int
    total_posts: int
    total_interactions: int
    total_follows: int
    average_followers: float
    average_following: float
    average_posts_per_agent: float
    network_density: float
    average_path_length: float
    clustering_coefficient: float


@dataclass
class AgentMetrics:
    """Agent-level metrics"""
    agent_id: str
    posts_count: int
    followers_count: int
    following_count: int
    likes_received: int
    comments_received: int
    shares_received: int
    engagement_rate: float  # (likes + comments + shares) / posts
    influence_score: float  # Based on followers and engagement


@dataclass
class TimeSeriesData:
    """Time series data point"""
    timestamp: str
    value: float
    label: str


class AnalyticsEngine:
    """
    Analytics engine for network and agent metrics.
    
    Calculates:
    - Network-level metrics
    - Agent-level metrics
    - Time series data
    - Trends and insights
    """
    
    def __init__(self, profile_manager: AgentProfileManager):
        """
        Initialize analytics engine.
        
        Args:
            profile_manager: Agent profile manager
        """
        self.profile_manager = profile_manager
    
    def get_network_metrics(self) -> NetworkMetrics:
        """
        Get network-level metrics.
        
        Returns:
            Network metrics
        """
        profiles = list(self.profile_manager.profiles.values())
        
        if not profiles:
            return NetworkMetrics(
                total_agents=0,
                total_posts=0,
                total_interactions=0,
                total_follows=0,
                average_followers=0.0,
                average_following=0.0,
                average_posts_per_agent=0.0,
                network_density=0.0,
                average_path_length=0.0,
                clustering_coefficient=0.0
            )
        
        total_agents = len(profiles)
        total_posts = sum(p.stats.get("posts_count", 0) for p in profiles)
        total_interactions = sum(
            p.stats.get("likes_received", 0) +
            p.stats.get("comments_received", 0) +
            p.stats.get("shares_received", 0)
            for p in profiles
        )
        total_follows = sum(p.stats.get("following_count", 0) for p in profiles)
        
        average_followers = sum(p.stats.get("followers_count", 0) for p in profiles) / total_agents
        average_following = total_follows / total_agents
        average_posts_per_agent = total_posts / total_agents if total_agents > 0 else 0.0
        
        # Network density (actual edges / possible edges)
        possible_edges = total_agents * (total_agents - 1) / 2
        network_density = total_follows / possible_edges if possible_edges > 0 else 0.0
        
        # Average path length (simplified - would use graph algorithms)
        average_path_length = 2.0  # Placeholder
        
        # Clustering coefficient (simplified)
        clustering_coefficient = 0.3  # Placeholder
        
        return NetworkMetrics(
            total_agents=total_agents,
            total_posts=total_posts,
            total_interactions=total_interactions,
            total_follows=total_follows,
            average_followers=average_followers,
            average_following=average_following,
            average_posts_per_agent=average_posts_per_agent,
            network_density=network_density,
            average_path_length=average_path_length,
            clustering_coefficient=clustering_coefficient
        )
    
    def get_agent_metrics(self, agent_id: str) -> Optional[AgentMetrics]:
        """
        Get agent-level metrics.
        
        Args:
            agent_id: Agent ID
            
        Returns:
            Agent metrics or None
        """
        profile = self.profile_manager.get_profile(agent_id)
        if not profile:
            return None
        
        posts_count = profile.stats.get("posts_count", 0)
        followers_count = profile.stats.get("followers_count", 0)
        following_count = profile.stats.get("following_count", 0)
        likes_received = profile.stats.get("likes_received", 0)
        comments_received = profile.stats.get("comments_received", 0)
        shares_received = profile.stats.get("shares_received", 0)
        
        # Engagement rate
        total_engagement = likes_received + comments_received + shares_received
        engagement_rate = total_engagement / posts_count if posts_count > 0 else 0.0
        
        # Influence score (weighted combination)
        influence_score = (
            0.4 * followers_count / 100.0 +  # Normalize to [0, 1]
            0.3 * engagement_rate +
            0.3 * (total_engagement / 100.0)  # Normalize to [0, 1]
        )
        influence_score = min(influence_score, 1.0)
        
        return AgentMetrics(
            agent_id=agent_id,
            posts_count=posts_count,
            followers_count=followers_count,
            following_count=following_count,
            likes_received=likes_received,
            comments_received=comments_received,
            shares_received=shares_received,
            engagement_rate=engagement_rate,
            influence_score=influence_score
        )
    
    def get_top_agents(
        self,
        metric: str = "followers",
        limit: int = 10
    ) -> List[AgentMetrics]:
        """
        Get top agents by metric.
        
        Args:
            metric: Metric to rank by (followers, engagement, influence)
            limit: Maximum number of results
            
        Returns:
            List of agent metrics
        """
        all_metrics = []
        
        for agent_id in self.profile_manager.profiles.keys():
            metrics = self.get_agent_metrics(agent_id)
            if metrics:
                all_metrics.append(metrics)
        
        # Sort by metric
        if metric == "followers":
            all_metrics.sort(key=lambda m: m.followers_count, reverse=True)
        elif metric == "engagement":
            all_metrics.sort(key=lambda m: m.engagement_rate, reverse=True)
        elif metric == "influence":
            all_metrics.sort(key=lambda m: m.influence_score, reverse=True)
        else:
            all_metrics.sort(key=lambda m: m.followers_count, reverse=True)
        
        return all_metrics[:limit]
    
    def get_growth_trends(
        self,
        days: int = 30
    ) -> Dict[str, List[TimeSeriesData]]:
        """
        Get growth trends over time.
        
        Args:
            days: Number of days to analyze
            
        Returns:
            Dictionary of metric -> time series data
        """
        # Simplified - would track historical data in production
        trends = {
            "agents": [],
            "posts": [],
            "interactions": [],
            "follows": []
        }
        
        # Generate placeholder data
        for i in range(days):
            timestamp = (datetime.utcnow() - timedelta(days=days-i)).isoformat()
            trends["agents"].append(TimeSeriesData(timestamp, 10.0 + i * 0.5, "agents"))
            trends["posts"].append(TimeSeriesData(timestamp, 50.0 + i * 2.0, "posts"))
            trends["interactions"].append(TimeSeriesData(timestamp, 100.0 + i * 5.0, "interactions"))
            trends["follows"].append(TimeSeriesData(timestamp, 20.0 + i * 1.0, "follows"))
        
        return trends
