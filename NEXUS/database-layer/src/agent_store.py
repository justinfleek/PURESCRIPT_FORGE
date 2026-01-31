"""
Nexus Database Layer - Agent Store
CRUD operations for agent configurations and states
"""

import sqlite3
from typing import List, Optional, Dict, Any
from dataclasses import dataclass, asdict
from datetime import datetime
import json
from pathlib import Path


@dataclass
class AgentRecord:
    """Agent record in database"""
    id: str
    agent_type: str  # web_search, content_extraction, network_formation
    config: Dict[str, Any]  # Agent configuration
    state: Dict[str, Any]  # Agent state
    status: str  # running, stopped, error
    created_at: str
    updated_at: str
    sandbox_config: Optional[Dict[str, Any]] = None
    working_dir: str = ""


class AgentStore:
    """
    Agent store for CRUD operations on agents.
    
    Stores agent configurations, states, and sandbox configurations.
    """
    
    def __init__(self, conn: sqlite3.Connection):
        """
        Initialize agent store.
        
        Args:
            conn: SQLite connection
        """
        self.conn = conn
    
    def save_agent(self, agent: AgentRecord) -> None:
        """
        Save agent to database.
        
        Args:
            agent: Agent record to save
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            INSERT OR REPLACE INTO agents (
                id, agent_type, config, state, status,
                created_at, updated_at, sandbox_config, working_dir
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
        """, (
            agent.id,
            agent.agent_type,
            json.dumps(agent.config),
            json.dumps(agent.state),
            agent.status,
            agent.created_at,
            agent.updated_at,
            json.dumps(agent.sandbox_config) if agent.sandbox_config else None,
            agent.working_dir
        ))
        self.conn.commit()
    
    def load_agent(self, agent_id: str) -> Optional[AgentRecord]:
        """
        Load agent from database.
        
        Args:
            agent_id: Agent ID
            
        Returns:
            Agent record or None if not found
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM agents WHERE id = ?
        """, (agent_id,))
        row = cursor.fetchone()
        
        if row is None:
            return None
        
        return AgentRecord(
            id=row["id"],
            agent_type=row["agent_type"],
            config=json.loads(row["config"]),
            state=json.loads(row["state"]),
            status=row["status"],
            created_at=row["created_at"],
            updated_at=row["updated_at"],
            sandbox_config=json.loads(row["sandbox_config"]) if row["sandbox_config"] else None,
            working_dir=row["working_dir"]
        )
    
    def update_agent_state(self, agent_id: str, state: Dict[str, Any]) -> None:
        """
        Update agent state.
        
        Args:
            agent_id: Agent ID
            state: New state dictionary
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            UPDATE agents
            SET state = ?, updated_at = ?
            WHERE id = ?
        """, (
            json.dumps(state),
            datetime.utcnow().isoformat(),
            agent_id
        ))
        self.conn.commit()
    
    def update_agent_status(self, agent_id: str, status: str) -> None:
        """
        Update agent status.
        
        Args:
            agent_id: Agent ID
            status: New status (running, stopped, error)
        """
        cursor = self.conn.cursor()
        cursor.execute("""
            UPDATE agents
            SET status = ?, updated_at = ?
            WHERE id = ?
        """, (
            status,
            datetime.utcnow().isoformat(),
            agent_id
        ))
        self.conn.commit()
    
    def list_agents(self, agent_type: Optional[str] = None, status: Optional[str] = None) -> List[AgentRecord]:
        """
        List agents, optionally filtered by type or status.
        
        Args:
            agent_type: Optional agent type filter
            status: Optional status filter
            
        Returns:
            List of agent records
        """
        cursor = self.conn.cursor()
        
        if agent_type and status:
            cursor.execute("""
                SELECT * FROM agents
                WHERE agent_type = ? AND status = ?
                ORDER BY created_at DESC
            """, (agent_type, status))
        elif agent_type:
            cursor.execute("""
                SELECT * FROM agents
                WHERE agent_type = ?
                ORDER BY created_at DESC
            """, (agent_type,))
        elif status:
            cursor.execute("""
                SELECT * FROM agents
                WHERE status = ?
                ORDER BY created_at DESC
            """, (status,))
        else:
            cursor.execute("""
                SELECT * FROM agents
                ORDER BY created_at DESC
            """)
        
        rows = cursor.fetchall()
        
        return [
            AgentRecord(
                id=row["id"],
                agent_type=row["agent_type"],
                config=json.loads(row["config"]),
                state=json.loads(row["state"]),
                status=row["status"],
                created_at=row["created_at"],
                updated_at=row["updated_at"],
                sandbox_config=json.loads(row["sandbox_config"]) if row["sandbox_config"] else None,
                working_dir=row["working_dir"]
            )
            for row in rows
        ]
    
    def delete_agent(self, agent_id: str) -> None:
        """
        Delete agent from database.
        
        Args:
            agent_id: Agent ID
        """
        cursor = self.conn.cursor()
        cursor.execute("DELETE FROM agents WHERE id = ?", (agent_id,))
        self.conn.commit()
    
    def count_agents(self, agent_type: Optional[str] = None, status: Optional[str] = None) -> int:
        """
        Count agents, optionally filtered by type or status.
        
        Args:
            agent_type: Optional agent type filter
            status: Optional status filter
            
        Returns:
            Number of agents
        """
        cursor = self.conn.cursor()
        
        if agent_type and status:
            cursor.execute("""
                SELECT COUNT(*) FROM agents
                WHERE agent_type = ? AND status = ?
            """, (agent_type, status))
        elif agent_type:
            cursor.execute("""
                SELECT COUNT(*) FROM agents
                WHERE agent_type = ?
            """, (agent_type,))
        elif status:
            cursor.execute("""
                SELECT COUNT(*) FROM agents
                WHERE status = ?
            """, (status,))
        else:
            cursor.execute("SELECT COUNT(*) FROM agents")
        
        return cursor.fetchone()[0]
