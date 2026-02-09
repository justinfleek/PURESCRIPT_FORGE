"""
Nexus Tests - Agent Social System
Comprehensive tests for agent social features
"""

import pytest
from datetime import datetime
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent / "agent-social" / "src"))
from agent_profile import AgentProfileManager, AgentProfile, AgentPost
from discovery import AgentDiscovery, Recommendation
from personality import PersonalityGenerator, Personality
from messaging import MessagingSystem, Message, Conversation
from analytics import AnalyticsEngine, NetworkMetrics, AgentMetrics
from content_moderation import ContentModerator, ModerationResult


class TestAgentProfile:
    """Tests for agent profiles"""
    
    def test_create_profile(self):
        """Test creating agent profile"""
        manager = AgentProfileManager()
        profile = manager.create_profile(
            agent_id="agent-1",
            username="test_agent",
            display_name="Test Agent",
            bio="Test bio",
            interests=["AI", "ML"],
            expertise=["Python", "PureScript"]
        )
        
        assert profile.agent_id == "agent-1"
        assert profile.username == "test_agent"
        assert profile.display_name == "Test Agent"
        assert len(profile.interests) == 2
        assert len(profile.expertise) == 2
    
    def test_create_post(self):
        """Test creating agent post"""
        manager = AgentProfileManager()
        manager.create_profile("agent-1", "test", "Test")
        
        post = manager.create_post(
            agent_id="agent-1",
            content="Test post",
            content_type="text",
            tags=["test"]
        )
        
        assert post.agent_id == "agent-1"
        assert post.content == "Test post"
        assert len(post.tags) == 1
        assert manager.profiles["agent-1"].stats["posts_count"] == 1
    
    def test_like_post(self):
        """Test liking a post"""
        manager = AgentProfileManager()
        manager.create_profile("agent-1", "test1", "Test 1")
        manager.create_profile("agent-2", "test2", "Test 2")
        
        post = manager.create_post("agent-1", "Test post")
        interaction = manager.like_post("agent-2", post.post_id)
        
        assert interaction.interaction_type == "like"
        assert post.stats["likes_count"] == 1
        assert manager.profiles["agent-1"].stats["likes_received"] == 1
    
    def test_follow_agent(self):
        """Test following an agent"""
        manager = AgentProfileManager()
        manager.create_profile("agent-1", "test1", "Test 1")
        manager.create_profile("agent-2", "test2", "Test 2")
        
        interaction = manager.follow_agent("agent-1", "agent-2")
        
        assert interaction.interaction_type == "follow"
        assert "agent-2" in manager.follows["agent-1"]
        assert "agent-1" in manager.followers["agent-2"]
        assert manager.profiles["agent-1"].stats["following_count"] == 1
        assert manager.profiles["agent-2"].stats["followers_count"] == 1
    
    def test_get_feed(self):
        """Test getting agent feed"""
        manager = AgentProfileManager()
        manager.create_profile("agent-1", "test1", "Test 1")
        manager.create_profile("agent-2", "test2", "Test 2")
        
        manager.follow_agent("agent-1", "agent-2")
        manager.create_post("agent-2", "Post from agent 2")
        manager.create_post("agent-1", "Post from agent 1")
        
        feed = manager.get_feed("agent-1")
        
        assert len(feed) == 2
        assert feed[0].agent_id == "agent-1"  # Most recent


class TestDiscovery:
    """Tests for agent discovery"""
    
    def test_discover_agents(self):
        """Test discovering agents"""
        manager = AgentProfileManager()
        manager.create_profile("agent-1", "test1", "Test 1", interests=["AI", "ML"])
        manager.create_profile("agent-2", "test2", "Test 2", interests=["AI", "Python"])
        manager.create_profile("agent-3", "test3", "Test 3", interests=["Music", "Art"])
        
        discovery = AgentDiscovery(manager)
        recommendations = discovery.discover_agents("agent-1", limit=2)
        
        assert len(recommendations) > 0
        assert recommendations[0].agent_id == "agent-2"  # Shared interests


class TestPersonality:
    """Tests for personality system"""
    
    def test_generate_personality(self):
        """Test generating personality"""
        generator = PersonalityGenerator()
        personality = generator.generate_personality("agent-1")
        
        assert personality.agent_id == "agent-1"
        assert len(personality.traits) > 0
        assert personality.communication_style in generator.communication_styles
    
    def test_influence_post_creation(self):
        """Test personality influencing post creation"""
        generator = PersonalityGenerator()
        personality = generator.generate_personality("agent-1")
        
        base_content = "test content"
        modified = generator.influence_post_creation(personality, base_content)
        
        assert len(modified) >= len(base_content)


class TestMessaging:
    """Tests for messaging system"""
    
    def test_send_message(self):
        """Test sending message"""
        messaging = MessagingSystem()
        message = messaging.send_message("agent-1", "agent-2", "Hello!")
        
        assert message.sender_id == "agent-1"
        assert message.recipient_id == "agent-2"
        assert message.content == "Hello!"
    
    def test_get_conversation(self):
        """Test getting conversation"""
        messaging = MessagingSystem()
        messaging.send_message("agent-1", "agent-2", "Hello!")
        messaging.send_message("agent-2", "agent-1", "Hi!")
        
        conversation = messaging.get_conversation("agent-1", "agent-2")
        
        assert conversation is not None
        assert len(conversation.messages) == 2


class TestAnalytics:
    """Tests for analytics"""
    
    def test_get_network_metrics(self):
        """Test getting network metrics"""
        manager = AgentProfileManager()
        manager.create_profile("agent-1", "test1", "Test 1")
        manager.create_profile("agent-2", "test2", "Test 2")
        manager.follow_agent("agent-1", "agent-2")
        
        analytics = AnalyticsEngine(manager)
        metrics = analytics.get_network_metrics()
        
        assert metrics.total_agents == 2
        assert metrics.total_follows == 1
    
    def test_get_agent_metrics(self):
        """Test getting agent metrics"""
        manager = AgentProfileManager()
        manager.create_profile("agent-1", "test1", "Test 1")
        manager.create_post("agent-1", "Test post")
        
        analytics = AnalyticsEngine(manager)
        metrics = analytics.get_agent_metrics("agent-1")
        
        assert metrics is not None
        assert metrics.posts_count == 1


class TestContentModeration:
    """Tests for content moderation"""
    
    def test_moderate_safe_content(self):
        """Test moderating safe content"""
        moderator = ContentModerator()
        result = moderator.moderate_content("This is a normal post about AI.")
        
        assert result.is_safe == True
    
    def test_moderate_spam(self):
        """Test moderating spam"""
        moderator = ContentModerator()
        result = moderator.moderate_content("Buy now! Click here! Limited time offer!")
        
        assert result.is_safe == False
        assert "spam" in result.reason.lower()
