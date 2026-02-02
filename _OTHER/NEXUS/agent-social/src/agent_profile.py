"""
Nexus Agent Social - Agent Profile
Agent profiles/pages for social media network
"""

from typing import List, Dict, Optional
from dataclasses import dataclass, field
from datetime import datetime
import uuid


@dataclass
class AgentProfile:
    """Agent profile/page"""
    agent_id: str
    username: str
    display_name: str
    bio: str
    avatar_url: Optional[str] = None
    cover_image_url: Optional[str] = None
    interests: List[str] = field(default_factory=list)
    expertise: List[str] = field(default_factory=list)
    personality_traits: Dict[str, float] = field(default_factory=dict)  # trait -> strength (0-1)
    created_at: str = ""
    updated_at: str = ""
    stats: Dict[str, int] = field(default_factory=dict)  # posts_count, followers_count, following_count, etc.
    metadata: Dict = field(default_factory=dict)


@dataclass
class AgentPost:
    """Agent post/content"""
    post_id: str
    agent_id: str
    content: str
    content_type: str  # text, link, image, video, discovery
    media_urls: List[str] = field(default_factory=list)
    tags: List[str] = field(default_factory=list)
    mentions: List[str] = field(default_factory=list)  # Agent IDs mentioned
    created_at: str = ""
    updated_at: str = ""
    stats: Dict[str, int] = field(default_factory=dict)  # likes_count, comments_count, shares_count
    metadata: Dict = field(default_factory=dict)


@dataclass
class AgentInteraction:
    """Agent interaction (like, comment, share, follow)"""
    interaction_id: str
    agent_id: str  # Agent performing interaction
    target_type: str  # post, agent, comment
    target_id: str
    interaction_type: str  # like, comment, share, follow
    content: Optional[str] = None  # For comments
    created_at: str = ""


class AgentProfileManager:
    """
    Agent profile manager for managing agent profiles/pages.
    
    Handles:
    - Profile creation/updates
    - Post creation
    - Interaction tracking
    - Statistics
    """
    
    def __init__(self):
        """Initialize profile manager"""
        self.profiles: Dict[str, AgentProfile] = {}
        self.posts: Dict[str, AgentPost] = {}
        self.interactions: Dict[str, AgentInteraction] = {}
        self.agent_posts: Dict[str, List[str]] = {}  # agent_id -> list of post_ids
        self.follows: Dict[str, set] = {}  # agent_id -> set of following agent_ids
        self.followers: Dict[str, set] = {}  # agent_id -> set of follower agent_ids
    
    def create_profile(
        self,
        agent_id: str,
        username: str,
        display_name: str,
        bio: str = "",
        interests: Optional[List[str]] = None,
        expertise: Optional[List[str]] = None
    ) -> AgentProfile:
        """
        Create agent profile.
        
        Args:
            agent_id: Agent ID
            username: Username
            display_name: Display name
            bio: Bio text
            interests: List of interests
            expertise: List of expertise areas
            
        Returns:
            Agent profile
        """
        profile = AgentProfile(
            agent_id=agent_id,
            username=username,
            display_name=display_name,
            bio=bio,
            interests=interests or [],
            expertise=expertise or [],
            created_at=datetime.utcnow().isoformat(),
            updated_at=datetime.utcnow().isoformat(),
            stats={
                "posts_count": 0,
                "followers_count": 0,
                "following_count": 0,
                "likes_received": 0,
                "comments_received": 0,
                "shares_received": 0
            }
        )
        
        self.profiles[agent_id] = profile
        self.agent_posts[agent_id] = []
        self.follows[agent_id] = set()
        self.followers[agent_id] = set()
        
        return profile
    
    def get_profile(self, agent_id: str) -> Optional[AgentProfile]:
        """
        Get agent profile.
        
        Args:
            agent_id: Agent ID
            
        Returns:
            Agent profile or None
        """
        return self.profiles.get(agent_id)
    
    def create_post(
        self,
        agent_id: str,
        content: str,
        content_type: str = "text",
        media_urls: Optional[List[str]] = None,
        tags: Optional[List[str]] = None
    ) -> AgentPost:
        """
        Create agent post.
        
        Args:
            agent_id: Agent ID
            content: Post content
            content_type: Content type
            media_urls: List of media URLs
            tags: List of tags
            
        Returns:
            Agent post
        """
        post = AgentPost(
            post_id=str(uuid.uuid4()),
            agent_id=agent_id,
            content=content,
            content_type=content_type,
            media_urls=media_urls or [],
            tags=tags or [],
            created_at=datetime.utcnow().isoformat(),
            updated_at=datetime.utcnow().isoformat(),
            stats={
                "likes_count": 0,
                "comments_count": 0,
                "shares_count": 0
            }
        )
        
        self.posts[post.post_id] = post
        
        if agent_id not in self.agent_posts:
            self.agent_posts[agent_id] = []
        self.agent_posts[agent_id].append(post.post_id)
        
        # Update profile stats
        if agent_id in self.profiles:
            self.profiles[agent_id].stats["posts_count"] += 1
        
        return post
    
    def like_post(self, agent_id: str, post_id: str) -> AgentInteraction:
        """
        Like a post.
        
        Args:
            agent_id: Agent ID performing like
            post_id: Post ID
            
        Returns:
            Interaction
        """
        interaction = AgentInteraction(
            interaction_id=str(uuid.uuid4()),
            agent_id=agent_id,
            target_type="post",
            target_id=post_id,
            interaction_type="like",
            created_at=datetime.utcnow().isoformat()
        )
        
        self.interactions[interaction.interaction_id] = interaction
        
        # Update post stats
        if post_id in self.posts:
            self.posts[post_id].stats["likes_count"] += 1
            
            # Update author stats
            author_id = self.posts[post_id].agent_id
            if author_id in self.profiles:
                self.profiles[author_id].stats["likes_received"] += 1
        
        return interaction
    
    def comment_post(
        self,
        agent_id: str,
        post_id: str,
        comment_content: str
    ) -> AgentInteraction:
        """
        Comment on a post.
        
        Args:
            agent_id: Agent ID commenting
            post_id: Post ID
            comment_content: Comment content
            
        Returns:
            Interaction
        """
        interaction = AgentInteraction(
            interaction_id=str(uuid.uuid4()),
            agent_id=agent_id,
            target_type="post",
            target_id=post_id,
            interaction_type="comment",
            content=comment_content,
            created_at=datetime.utcnow().isoformat()
        )
        
        self.interactions[interaction.interaction_id] = interaction
        
        # Update post stats
        if post_id in self.posts:
            self.posts[post_id].stats["comments_count"] += 1
            
            # Update author stats
            author_id = self.posts[post_id].agent_id
            if author_id in self.profiles:
                self.profiles[author_id].stats["comments_received"] += 1
        
        return interaction
    
    def follow_agent(self, agent_id: str, target_agent_id: str) -> AgentInteraction:
        """
        Follow another agent.
        
        Args:
            agent_id: Agent ID following
            target_agent_id: Agent ID to follow
            
        Returns:
            Interaction
        """
        interaction = AgentInteraction(
            interaction_id=str(uuid.uuid4()),
            agent_id=agent_id,
            target_type="agent",
            target_id=target_agent_id,
            interaction_type="follow",
            created_at=datetime.utcnow().isoformat()
        )
        
        self.interactions[interaction.interaction_id] = interaction
        
        # Update follow relationships
        if agent_id not in self.follows:
            self.follows[agent_id] = set()
        self.follows[agent_id].add(target_agent_id)
        
        if target_agent_id not in self.followers:
            self.followers[target_agent_id] = set()
        self.followers[target_agent_id].add(agent_id)
        
        # Update stats
        if agent_id in self.profiles:
            self.profiles[agent_id].stats["following_count"] += 1
        if target_agent_id in self.profiles:
            self.profiles[target_agent_id].stats["followers_count"] += 1
        
        return interaction
    
    def get_feed(self, agent_id: str, limit: int = 50) -> List[AgentPost]:
        """
        Get feed for agent (posts from followed agents + own posts).
        
        Args:
            agent_id: Agent ID
            limit: Maximum number of posts
            
        Returns:
            List of posts (sorted by recency)
        """
        # Get followed agents
        followed_agents = self.follows.get(agent_id, set())
        followed_agents.add(agent_id)  # Include own posts
        
        # Collect posts from followed agents
        feed_posts = []
        for followed_id in followed_agents:
            post_ids = self.agent_posts.get(followed_id, [])
            for post_id in post_ids:
                if post_id in self.posts:
                    feed_posts.append(self.posts[post_id])
        
        # Sort by creation time (newest first)
        feed_posts.sort(key=lambda p: p.created_at, reverse=True)
        
        return feed_posts[:limit]
    
    def get_profile_posts(self, agent_id: str, limit: int = 50) -> List[AgentPost]:
        """
        Get posts from agent profile.
        
        Args:
            agent_id: Agent ID
            limit: Maximum number of posts
            
        Returns:
            List of posts
        """
        post_ids = self.agent_posts.get(agent_id, [])
        posts = [self.posts[pid] for pid in post_ids if pid in self.posts]
        posts.sort(key=lambda p: p.created_at, reverse=True)
        return posts[:limit]
