-- | NEXUS Social Network Properties Proofs
-- | Mathematically proven properties about social network feeds
-- |
-- | Strategy: Encode feed construction with type-level invariants.
-- | Properties follow from the construction logic.

import Lean
import Std.Data.List.Lemmas

-- | Agent ID
structure AgentId where
  id : String
  deriving DecidableEq, BEq, Repr

-- | Post ID
structure PostId where
  id : String
  deriving DecidableEq, BEq, Repr

-- | Agent post
structure Post where
  postId : PostId
  agentId : AgentId
  content : String
  deriving DecidableEq, Repr

-- | Feed with consistency invariant
-- | All posts must be from followed agents or the viewer themselves
structure Feed where
  viewerId : AgentId
  followedAgents : List AgentId
  posts : List Post
  h_posts_valid : ∀ post ∈ posts,
    post.agentId ∈ followedAgents ∨ post.agentId = viewerId
  deriving Repr

/-!
## Feed Construction

Smart constructors that maintain invariants by construction.
-/

-- | Create an empty feed
def emptyFeed (viewer : AgentId) (following : List AgentId) : Feed where
  viewerId := viewer
  followedAgents := following
  posts := []
  h_posts_valid := by intro post h; exact False.elim (List.not_mem_nil post h)

-- | Add a post to feed (with validation)
def addPost (feed : Feed) (post : Post)
  (h_valid : post.agentId ∈ feed.followedAgents ∨ post.agentId = feed.viewerId) : Feed where
  viewerId := feed.viewerId
  followedAgents := feed.followedAgents
  posts := post :: feed.posts
  h_posts_valid := by
    intro p h_p
    cases List.mem_cons.mp h_p with
    | inl h_eq =>
      rw [h_eq]
      exact h_valid
    | inr h_in_old =>
      exact feed.h_posts_valid p h_in_old

-- | Filter posts by author
def filterByAuthor (feed : Feed) (author : AgentId) : List Post :=
  feed.posts.filter (·.agentId == author)

-- | Collect posts from a list of agents (used to build feed)
def collectPosts (allPosts : List Post) (viewer : AgentId) (following : List AgentId) : Feed where
  viewerId := viewer
  followedAgents := following
  posts := allPosts.filter (fun p => p.agentId ∈ following || p.agentId == viewer)
  h_posts_valid := by
    intro post h_post
    simp [List.mem_filter] at h_post
    have ⟨_, h_valid⟩ := h_post
    cases Bool.or_eq_true.mp h_valid with
    | inl h_in =>
      left
      simp [List.elem_eq_mem, List.mem_iff_elem.mp] at h_in
      exact h_in
    | inr h_eq =>
      right
      exact beq_eq_true_iff_eq.mp h_eq

-- | Follow an agent (adds to followed list)
def followAgent (feed : Feed) (agent : AgentId) : Feed where
  viewerId := feed.viewerId
  followedAgents := agent :: feed.followedAgents
  posts := feed.posts
  h_posts_valid := by
    intro post h_post
    have h := feed.h_posts_valid post h_post
    cases h with
    | inl h_in =>
      left
      exact List.mem_cons_of_mem agent h_in
    | inr h_eq =>
      right
      exact h_eq

/-!
## Proven Properties

All properties follow mathematically from the type-level invariants.
-/

-- | Theorem: Feed consistency
-- | All posts in feed are from followed agents or the viewer
theorem feed_consistency (feed : Feed) :
  ∀ post ∈ feed.posts,
    post.agentId ∈ feed.followedAgents ∨ post.agentId = feed.viewerId :=
  feed.h_posts_valid

-- | Theorem: Post ownership
-- | Each post has exactly one owner (the agentId field)
theorem post_ownership (post : Post) :
  ∃! agent : AgentId, post.agentId = agent := by
  use post.agentId
  constructor
  · rfl
  · intro y h
    exact h.symm

-- | Theorem: Viewer's posts are always valid
-- | The viewer can always see their own posts
theorem viewer_posts_valid (feed : Feed) (post : Post) :
  post.agentId = feed.viewerId →
  (post.agentId ∈ feed.followedAgents ∨ post.agentId = feed.viewerId) := by
  intro h
  right
  exact h

-- | Theorem: Followed agent posts are valid
-- | Posts from followed agents are valid for the feed
theorem followed_posts_valid (feed : Feed) (post : Post) :
  post.agentId ∈ feed.followedAgents →
  (post.agentId ∈ feed.followedAgents ∨ post.agentId = feed.viewerId) := by
  intro h
  left
  exact h

-- | Theorem: Empty feed has no posts
theorem empty_feed_no_posts (viewer : AgentId) (following : List AgentId) :
  (emptyFeed viewer following).posts = [] := rfl

-- | Theorem: Empty feed preserves viewer
theorem empty_feed_preserves_viewer (viewer : AgentId) (following : List AgentId) :
  (emptyFeed viewer following).viewerId = viewer := rfl

-- | Theorem: Adding post increases count
theorem add_post_increases_count (feed : Feed) (post : Post)
  (h_valid : post.agentId ∈ feed.followedAgents ∨ post.agentId = feed.viewerId) :
  (addPost feed post h_valid).posts.length = feed.posts.length + 1 := by
  simp [addPost]

-- | Theorem: New post is in feed after adding
theorem new_post_in_feed (feed : Feed) (post : Post)
  (h_valid : post.agentId ∈ feed.followedAgents ∨ post.agentId = feed.viewerId) :
  post ∈ (addPost feed post h_valid).posts := by
  simp [addPost]

-- | Theorem: Following preserves existing posts
theorem follow_preserves_posts (feed : Feed) (agent : AgentId) :
  (followAgent feed agent).posts = feed.posts := rfl

-- | Theorem: Following adds agent to followed list
theorem follow_adds_agent (feed : Feed) (agent : AgentId) :
  agent ∈ (followAgent feed agent).followedAgents := by
  simp [followAgent]

-- | Theorem: Following preserves previously followed agents
theorem follow_preserves_following (feed : Feed) (agent newAgent : AgentId) :
  agent ∈ feed.followedAgents →
  agent ∈ (followAgent feed newAgent).followedAgents := by
  intro h
  simp [followAgent, h]

-- | Theorem: Filter by author returns only that author's posts
theorem filter_by_author_correct (feed : Feed) (author : AgentId) :
  ∀ post ∈ filterByAuthor feed author, post.agentId = author := by
  intro post h
  simp [filterByAuthor, List.mem_filter] at h
  exact beq_eq_true_iff_eq.mp h.2

-- | Theorem: Collected posts satisfy feed invariant
theorem collect_posts_valid (allPosts : List Post) (viewer : AgentId) (following : List AgentId) :
  ∀ post ∈ (collectPosts allPosts viewer following).posts,
    post.agentId ∈ following ∨ post.agentId = viewer :=
  (collectPosts allPosts viewer following).h_posts_valid

